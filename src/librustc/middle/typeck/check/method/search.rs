// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Method search framework that is used for finding which methods
 * apply to the receiver, given appropriate adjustments. See doc.rs
 * or method comments for more details.
 */

use extra::list::Nil;
use middle::ty;
use middle::typeck::check;
use middle::typeck::check::method;
use middle::typeck::check::method::get_mode_from_explicit_self;
use middle::typeck::check::method::LookupContext;
use middle::typeck::check::regionmanip;
use middle::typeck::check::vtable;
use middle::typeck::infer;
use middle::typeck::method_map_entry;
use middle::typeck::method_origin;
use middle::typeck::method_param;
use middle::typeck::method_static;
use middle::typeck::method_self;
use middle::typeck::method_super;
use middle::typeck::method_trait;
use middle::subst::Subst;
use syntax::ast;
use util::ppaux::Repr;

///////////////////////////////////////////////////////////////////////////
// Types

pub enum RcvrType {
    SizedType(ty::t),                         // T
    ExistentialType(ast::def_id, ty::substs), // Trait
    VectorType(ty::t),                        // [T]
    StringType,                               // str
}

struct RcvrAdjustment {
    autoderefs: uint,
    autoslice: Option<(ty::Region, ast::mutability)>
}

pub trait MethodSearch {
    fn push_candidates(&mut self,
                       lookupcx: &method::LookupContext,
                       rcvr_ty: &RcvrType,
                       out: &mut ~[Candidate]);
}

#[deriving(Clone)]
pub struct Candidate {
    rcvr_substs: ty::substs,
    method_ty: @ty::Method,
    origin: method_origin,
}

pub enum SearchError {
    StaticMethodCalled,
    NotManaged, // `@self` method invoked on non-pointer receiver
    NotOwned, // `~self` method invoked on non-pointer receiver
    ExpectedFound(ty::t, ty::t, ty::type_err),
    UnsizedReceiverWithByValueMethod, // by-value method on unsized type
    ObjectMethodReferencingSelf, // object method called with `Self` type
    ObjectMethodGeneric, // object method called with type params
    DropTraitMethod,
    IncorrectNumberOfTypeParameters(uint, uint),
    MultipleCandidates(~[Candidate]),
}

enum SearchResult {
    NoMethodFound,
    MethodFound(method_map_entry),
    Error(SearchError)
}

///////////////////////////////////////////////////////////////////////////
// Methods

impl<'self> method::LookupContext<'self> {
    pub fn do_search<M:MethodSearch>(&mut self,
                                     start_ty: ty::t,
                                     mut search: M)
                                     -> SearchResult {
        /*!
         * Overarching search routine. Given the search routine `search`,
         * determines whether any candidates can be found by applying
         * automatic adjustments to `start_ty`, which is the unadjusted
         * type of the receiver.
         */

        let mut dids = ~[];
        let mut rcvr_tys = ~[SizedType(start_ty)];
        let mut candidates = ~[];

        loop {
            search.push_candidates(self, rcvr_tys.last(), &mut candidates);
            if !candidates.is_empty() {
                let adjustment = RcvrAdjustment {
                    autoderefs: rcvr_tys.len() - 1,
                    autoslice: None
                };
                return self.candidates_found(rcvr_tys, candidates, adjustment);
            }

            match self.deref(rcvr_tys.last(), &mut dids) {
                None => {
                    return self.search_slice(rcvr_tys, &mut search);
                }
                Some(t) => {
                    rcvr_tys.push(t);
                }
            }
        }
    }

    fn deref(&mut self,
             rcvr_ty: &RcvrType,
             dids: &mut ~[ast::def_id])
             -> Option<RcvrType> {
        /*!
         * Attempts to deref the type `rcvr_ty`, yielding result type.
         */

        let ty = match *rcvr_ty {
            SizedType(ty) => ty,
            ExistentialType(*) | VectorType(*) | StringType(*) => {
                return None;
            }
        };

        match ty::get(ty).sty {
            ty::ty_trait(def_id, ref substs, _, _, _) => {
                return Some(ExistentialType(def_id, substs.clone()));
            }
            ty::ty_evec(mt, _) => {
                return Some(VectorType(mt.ty));
            }
            ty::ty_estr(_) => {
                return Some(StringType);
            }
            ty::ty_enum(did, _) | ty::ty_struct(did, _) => {
                // Watch out for newtype'd enums like "struct T(@T)",
                // which could induce an infinite loop. See discussion
                // in typeck::check::do_autoderef().
                if dids.contains(&did) {
                    return None;
                }
                dids.push(did);
            }
            _ => {}
        }

        return match ty::deref(self.tcx(), ty, false) {
            None => {
                None
            }
            Some(t) => {
                let t_r = check::structurally_resolved_type(self.fcx,
                                                            self.self_expr.span,
                                                            t.ty);
                Some(SizedType(t_r))
            }
        };
    }

    fn search_slice<M:MethodSearch>(&mut self,
                                    rcvr_tys: &[RcvrType],
                                    search: &mut M)
                                    -> SearchResult {
        /*!
         * Considers conversions from `~[]` or `@[]` to `&[]`.
         * The existence of this method is quite unfortunate.  The
         * problem is that if we have a receiver type like `~[T]`,
         * there may be a trait impls defined on `&[T]` or `&mut [T]`
         * and we would to use a method from it (the same holds for
         * `~Object/&Object` or `~str/&str`. If the DST proposal were
         * done, this would fall out from the rules above, because
         * people would implement the trait for `[T]`, not `&[T]`. But
         * right now people can't do that, so we need some
         * special-case hokum to make it work (this method).
         *
         * Basically, if we wind up with a final receiver type is no
         * sized (e.g., `[T]`, `Trait`, etc), we will do some final
         * searches for possible matches. For example, assuming result
         * is `[T]`, we would search for `&const [T]`, `&[T]`, `&mut
         * [T]`, and even `&&[T]` etc (which occurs when you have an
         * `&self` method implemented for `&[T]`). Note that, unlike
         * the normal path, we have to exhaustively search through the
         * mutability qualifiers, because we can't derive it from the
         * self-type of the candidate as we normally do.
         *
         * The necessity of this routine is proof enough to me
         * that DST is a good idea! - nmatsakis
         */

        let tcx = self.tcx();
        match *rcvr_tys.last() {
            SizedType(*) => {
                NoMethodFound
            }

            ExistentialType(*) => {
                // We never handled this case before, hopefully we can
                // implement DST before it becomes important!
                NoMethodFound
            }

            VectorType(t_elem) => {
                // First try [T] to &m [T]
                match self.search_repeating_type(
                    search,
                    rcvr_tys,
                    [ast::m_const, ast::m_imm, ast::m_mutbl],
                    |r, m| ty::mk_evec(self.tcx(),
                                       ty::mt {mutbl: m, ty: t_elem},
                                       ty::vstore_slice(r)),
                    |r, m| ty::AutoBorrowVec(r, m))
                {
                    NoMethodFound => { /* Keep searching */ }
                    r @ MethodFound(*) | r @ Error(*) => { return r; }
                }

                // Then try [T] to &&m [T]. This horrible hack is
                // needed for calling &self methods implemented on
                // &[T] on an ~[T] receiver.  DST! DST!
                self.search_repeating_type(
                    search,
                    rcvr_tys,
                    [ast::m_const, ast::m_imm, ast::m_mutbl],
                    |r, m| {
                        let slice_ty = ty::mk_evec(self.tcx(),
                                                   ty::mt {mutbl: m, ty: t_elem},
                                                   ty::vstore_slice(r));
                        // NB: we do not try to autoref to a mutable
                        // pointer. That would be creating a pointer
                        // to a temporary pointer (the borrowed
                        // slice), so any update the callee makes to
                        // it can't be observed.
                        ty::mk_rptr(tcx, r, ty::mt {ty:slice_ty,
                                                    mutbl:ast::m_imm})
                    },
                    |r, m| ty::AutoBorrowVecRef(r, m))
            }

            StringType => {
                self.search_repeating_type(
                    search,
                    rcvr_tys,
                    [ast::m_imm],
                    |r, _| ty::mk_estr(self.tcx(),
                                       ty::vstore_slice(r)),
                    |r, m| ty::AutoBorrowVecRef(r, m))
            }
        }
    }

    fn search_repeating_type<M:MethodSearch>(
        &mut self,
        search: &mut M,
        rcvr_tys: &[RcvrType],
        mutabilities: &[ast::mutability],
        mk_ty: &fn(ty::Region, ast::mutability) -> ty::t,
        mk_ref: &fn(ty::Region, ast::mutability) -> ty::AutoRef)
        -> SearchResult
    {
        /*!
         * See `search_slice` above.
         */

        let region =
            self.infcx().next_region_var(
                infer::Autoref(self.expr.span));
        let mut candidates = ~[];
        for mutabilities.iter().advance |&mutbl| {
            let slice_rcvr_ty = SizedType(mk_ty(region, mutbl));
            search.push_candidates(self, &slice_rcvr_ty, &mut candidates);
            if candidates.is_empty() { loop; }

            let adjustment = RcvrAdjustment {
                autoderefs: rcvr_tys.len() - 1,
                autoslice: Some(mk_ref(region, mutbl))
            };
            return self.candidates_found(~[slice_rcvr_ty],
                                         candidates,
                                         adjustment);
        }
        NoMethodFound
    }

    fn candidates_found(&mut self,
                        rcvr_tys: ~[RcvrType],
                        mut candidates: ~[Candidate],
                        adjustment: RcvrAdjustment)
                        -> SearchResult {
        /*!
         * Called when we have a non-empy list of candidate methods.
         * `rcvr_tys` is the stack of receiver types that we have
         * auto-deref'd, and `adjustment` is the final adjustment applied
         * to the top of the stack (last element in the vector).
         */

        assert!(!candidates.is_empty());

        if candidates.len() > 1 {
            candidates = self.merge_candidates(candidates);
            if candidates.len() > 1 {
                return Error(MultipleCandidates(candidates));
            }
        }

        let candidate = candidates.pop();
        self.adjust_for_self_type_of_candidate(rcvr_tys, candidate, adjustment)
    }

    fn merge_candidates(&self, candidates: ~[Candidate]) -> ~[Candidate] {
        /*!
         * In some cases we wind up with multiple candidates that are
         * in fact the same method. For example, parameters may have the
         * same bound appear more than once, particularly with super
         * traits. This routine purges any duplicates and returns a new
         * vector.
         */

        let mut merged = ~[];
        let mut i = 0;
        while i < candidates.len() {
            let candidate_a = &candidates[i];

            let mut skip = false;

            let mut j = i + 1;
            while j < candidates.len() {
                let candidate_b = &candidates[j];
                debug!("attempting to merge %? and %?",
                       candidate_a, candidate_b);
                let candidates_same = match (&candidate_a.origin,
                                             &candidate_b.origin) {
                    (&method_param(ref p1), &method_param(ref p2)) => {
                        let same_trait = p1.trait_id == p2.trait_id;
                        let same_method = p1.method_num == p2.method_num;
                        let same_param = p1.param_num == p2.param_num;
                        // The bound number may be different because
                        // multiple bounds may lead to the same trait
                        // impl
                        same_trait && same_method && same_param
                    }
                    (&method_static(did1), &method_static(did2)) => {
                        did1 == did2
                    }
                    _ => false
                };
                if candidates_same {
                    skip = true;
                    break;
                }
                j += 1;
            }

            i += 1;

            if skip {
                // There are more than one of these and we need only one
                loop;
            } else {
                merged.push(candidate_a.clone());
            }
        }

        return merged;
    }

    fn adjust_for_self_type_of_candidate(&mut self,
                                         rcvr_tys: ~[RcvrType],
                                         candidate: Candidate,
                                         adjustment: RcvrAdjustment)
                                         -> SearchResult {
        /*!
         * Given that we have found the candidate method, adjusts
         * the receiver as indicated by the self type on that method.
         * See the `adjust_for_*_candidate` methods for more details
         * on how any particular self type is handled.
         */

        assert!(!rcvr_tys.is_empty());
        match candidate.method_ty.explicit_self {
            ast::sty_static => {
                Err(StaticMethodCalled)
            }

            ast::sty_value => {
                self.adjust_for_by_value_candidate(rcvr_tys.pop(),
                                                   candidate,
                                                   adjustment)
            }

            ast::sty_region(_, mutbl) => {
                self.adjust_for_borrowed_candidate(rcvr_tys.pop(),
                                                   candidate,
                                                   mutbl,
                                                   adjustment)
            }

            ast::sty_box(_) => {
                self.adjust_for_boxed_candidate(rcvr_tys,
                                                candidate,
                                                adjustment,
                                                NotManaged)
            }

            ast::sty_uniq(_) => {
                self.adjust_for_boxed_candidate(rcvr_tys,
                                                candidate,
                                                adjustment,
                                                NotOwned)
            }
        }
    }

    fn adjust_for_by_value_candidate(&mut self,
                                     rcvr_ty: RcvrType,
                                     candidate: Candidate,
                                     adjustment: RcvrAdjustment)
                                     -> SearchResult {
        /*!
         * Handles calls to method declared with `fn(self)`.
         * Such methods are legal if the receiver type is
         * sized.
         */

        match rcvr_ty {
            SizedType(t) => {
                let auto_adj = RcvrAdjustment {
                    autoderefs:
                        adjustment.autoderefs,
                    autoref:
                        adjustment.autoslice.map(
                            |&(r, m)| ty::AutoBorrowVec(r, m))
                };

                self.test_any_candidate(t, candidate, auto_adj)
            }

            ExistentialType(*) | VectorType(*) | StringType => {
                return Err(UnsizedReceiverWithByValueMethod);
            }
        }
    }

    fn adjust_for_borrowed_candidate(&mut self,
                                     rcvr_ty: RcvrType,
                                     mutbl: ast::mutability,
                                     candidate: Candidate,
                                     adjustment: RcvrAdjustment)
                                     -> SearchResult {
        /*!
         * Handles calls to method declared with `fn(&self)`.
         * We know that by using the adjustment `adjustment` we can
         * obtain a receiver of type `Self`, but we want a receiver
         * of type `&Self`. Therefore, we will "auto-ref", meaning that
         * we borrow the receiver we have thus far.
         *
         * Note that the receiver we have thus far may be an
         * autoderef'd region pointer already. This is
         * intentional; it is generally preferable to reborrow pointers
         * because it helps the borrow checker to know when the callee
         * no longer has access to the data. This is most important for
         * `&mut` pointers.
         *
         * For example, assume we invoke an `&mut self` method on a
         * receiver `r` of type `&mut T`. We wish to have the call be
         * the equivalent of `(&mut *r).method()`; that is, we want to
         * explicitly reborrow so that `r` is not consumed.
         * In this example, at the point where we enter this method,
         * we will have autoderef'd once, so we have effectively a
         * receiver of `*r`. This method then adds the `&mut`
         * operation.
         *
         * Note that reborrowing like this never produces a type error
         * that would not have otherwise occurred. If the lifetime of
         * the reborrow is the same as the lifetime of the original
         * pointer, then it is as if the original pointer were moved
         * into the callee.
         *
         * As another example, consider calling a `&self` method on a
         * receiver `r` of type `@@T`. Because the method is defined
         * on the type `T`, when we arrive at this point, `r` will
         * have been deref'd twice, leaving `**r`. We will then add
         * the `&`, yielding the final result of `&**r`.
         *
         * One annoying subtlety concerns the case where we have borrowed
         * `~[T]` to `&[T]`. In that case, we are auto-borrowing this
         * temporary slice. That is handled by using the `AutoBorrowVecRef`
         * adjustment, which bundles the two operations together.
         */

        let (region, auto_adj) = match adjustment.autoslice {
            None => {
                let region = self.infcx().next_region_var_nb(self.expr.span);

                // More pain caused by lack of DST. We can't just
                // "autoptr" an object type, we have to use
                // `AutoBorrowObj`
                match *rcvr_ty {
                    ExistentialType(*) => {
                        (region,
                         ty::AutoDerefRef {
                             autoderefs: adjustment.autoderefs - 1,
                             autoref: Some(ty::AutoBorrowObj(region, mutbl))})
                    }

                    _ => {
                        (region,
                         ty::AutoDerefRef {
                             autoderefs: adjustment.autoderefs,
                             autoref: Some(ty::AutoPtr(region, mutbl))})
                    }
                }
            }

            Some((r, m)) if mutbl == ast::m_imm => {
                // NB: We don't let user borrow from `~[]` to `&mut &[]`,
                // though we could safely do so. It's just kind of a footgun,
                // since the mutable effects of the method would affect
                // a temporary.
                (r, ty::AutoDerefRef {autoderefs: adjustment.autoderefs,
                                      autoref: Some(ty::AutoBorrowVecRef(r, m))})
            }

            Some((_, _)) => {
                return NoMethodFound;
            }
        };

        let tcx = self.tcx();
        let rptr_ty = match *rcvr_ty {
            SizedType(t) => {
                ty::mk_rptr(tcx, region, ty::mt {ty: t, mutbl: mutbl})
            }
            ExistentialType(def_id, substs) => {
                ty::mk_trait(tcx, def_id, substs,
                             ty::RegionTraitStore(region), mutbl)
            }

            // In fact, these cases cannot occur right now, because
            // there are never inherent methods or traits defined on
            // a type like `[T]`. But I still handle them.
            VectorType(t) => {
                ty::mk_evec(tcx, ty::mt {ty: t, mutbl: mutbl},
                            ty::vstore_slice(region))
            }
            StringType => {
                assert_eq!(mutbl, ast::m_imm);
                ty::mk_estr(tcx, ty::vstore_slice(region))
            }
        };

        self.evaluate_candidate(rptr_ty, candidate, auto_adj)
    }

    fn adjust_for_boxed_candidate(&mut self,
                                  rcvr_tys: ~[RcvrType],
                                  candidate: Candidate,
                                  adjustment: RcvrAdjustment,
                                  err_if_not_derefd: SearchError)
                                  -> SearchResult {
        /*!
         * Handles the case of an `@self` or `~self` receiver.
         * These are somewhat different from the `self` or `&self`
         * receivers because we cannot "recover" an `@T` value given
         * a `T` value (well, we could allocate a new box, but that's
         * not what the user wanted). So in fact we are not interested
         * in the *fully autoderef'd* value but rather the value that
         * we had one step before.
         *
         * To see what I mean, consider an `@self` method invoked
         * on an `@T` receiver `r` (the method is defined on `T`). At this
         * point, the adjusted receiver will be `*r`, since that has
         * the type `T`. We effectively want to drop this autoderef, yielding
         * `r` again.
         *
         * Note that the result may not always be compatible with the
         * expected type of the method (but this is ok). For example,
         * consider an `@self` method invoked on an `~T` receiver `r`.
         * We will drop the autoderef here to yield the receiver `r`.
         * The routine `evaluate_candidate()` that we invoke will
         * then test that `r` has an appropriate type (that is,
         * `@T`). This check will fail and an error will be reported.
         *
         * If we get to this point and there have not been any
         * autoderefs, indicated by `rcvr_tys` being of length 1, then
         * we know simply report an error. An example where this could
         * occur is if we invoked an `@self` method defined on the
         * type `T` on a receiver `r` of type `T`. Another example would
         * be an `@self` method defined on the type `&[]` and a receiver
         * of type `~[]` or `@[]`. In that case, we will coerce the `@[]`
         * to `&[]` but we will not box that temporary to get `@&[]`.
         */

        // If the receive has never been autoderef'd, then we can't
        // have a `@T` or `~T` receiver, so report an error!
        if rcvr_tys.len() <= 1 {
            return Err(err_if_not_derefd);
        }

        // Otherwise, because the receiver HAS been autoderef'd,
        // we know that autoslice is none, since we never autoderef
        // when we do the @[] -> &[] conversion.
        assert!(adjustment.autoderefs > 0);
        assert_eq!(adjustment.autoslice, None);

        // Convert autoadjustment to include one fewer autoderef.
        let auto_adj = ty::AutoDerefRef {autoderefs: adjustment.autoderefs - 1,
                                         autoref: None};

        // Find the type before the last autoderef; it must be a sized
        // type, since no unsized types are autoderefable.
        let self_ty = match rcvr_tys[rcvr_tys.len() - 1] {
            SizedType(ty) => ty,
            r => {
                self.tcx().sess.span_bug(
                    self.expr.span,
                    fmt!("Removing an autoderef yielded unsized type: %?", r));
            }
        };

        // Test to see if this type meets the self type of the candidate.
        self.evaluate_candidate(self_ty, candidate, auto_adj)
    }

    fn evaluate_candidate(&mut self,
                          adj_self_ty: ty::t,
                          candidate: Candidate,
                          auto_adj: ty::AutoDerefRef)
                          -> SearchResult {
        /*!
         * Now that we have adjusted for the self type of the candidate,
         * This routine tests that the type of the receiver we have is a
         * subtype of the self type expected by the candidate. This is
         * almost always true, because otherwise we would not have unearthed
         * the candidate during our searches in the first place, but there
         * are some cases where the check is still necessary.
         * For example, if the method has an `@self` or `~self` declaration,
         * this check is the one which ensures that
         * the actual receiver is managed or owned, respectively.
         * Assuming that the receiver check passes, the routine then
         * instantiates the method type and constructs and returns
         * the final search result.
         *
         * # Parameters
         *
         * - `adj_self_ty` is the final, adjusted type of the receiver
         * - `candidate` is the candidate method to be tested
         * - `auto_adj` is the set of adjustments that need to be
         *   performed to yield the type `adj_self_ty`
         */

        let tcx = self.tcx();
        let fty = self.fn_ty_from_origin(&candidate.origin);

        debug!("evaluate_candidate(expr=%s, candidate=%s, fty=%s)",
               self.expr.repr(tcx),
               self.cand_to_str(candidate),
               self.ty_to_str(fty));

        // Check for various error conditions:
        match self.enforce_object_limitations(fty, candidate) {
            Ok(()) => {}
            Err(e) => { return Error(e); }
        }

        match self.enforce_drop_trait_limitations(candidate) {
            Ok(()) => {}
            Err(e) => { return Error(e); }
        }

        // static methods should never have gotten this far:
        assert!(candidate.method_ty.explicit_self != ast::sty_static);

        // Find the "transformed" self type, meaning the self type
        // after the explicit self declaration is taken into account.
        let transformed_self_ty = match candidate.origin {
            method_trait(trait_def_id, _) => {
                self.construct_transformed_self_ty_for_object(
                    trait_def_id, candidate)
            }
            _ => {
                let t = candidate.method_ty.transformed_self_ty.get();
                t.subst(tcx, &candidate.rcvr_substs)
            }
        };

        // Determine the values for the type parameters of the method.
        // If they were not explicitly supplied, just construct fresh
        // type variables.
        let num_supplied_tps = self.supplied_tps.len();
        let num_method_tps = candidate.method_ty.generics.type_param_defs.len();
        let m_substs = {
            if num_supplied_tps == 0u {
                self.fcx.infcx().next_ty_vars(num_method_tps)
            } else if num_supplied_tps != num_method_tps {
                return Err(IncorrectNumberOfTypeParameters(num_method_tps,
                                                           num_supplied_tps));
            } else {
                self.supplied_tps.to_vec()
            }
        };

        // Construct the full set of type parameters for the method,
        // which is equal to the class tps + the method tps.
        let all_substs = ty::substs {
            tps: candidate.rcvr_substs.tps.clone().append(m_substs),
            ..candidate.rcvr_substs.clone()
        };

        // Compute the method type with type parameters substituted
        debug!("fty=%s all_substs=%s", fty.repr(tcx), all_substs.repr(tcx));
        let fty = fty.subst(tcx, &all_substs);
        debug!("after subst, fty=%s", self.ty_to_str(fty));

        // Replace any bound regions that appear in the function
        // signature with region variables
        let bare_fn_ty = match ty::get(fty).sty {
            ty::ty_bare_fn(ref f) => f.clone(),
            ref s => {
                tcx.sess.span_bug(
                    self.expr.span,
                    fmt!("Invoking method with non-bare-fn ty: %?", s));
            }
        };
        let (_, opt_transformed_self_ty, fn_sig) =
            regionmanip::replace_bound_regions_in_fn_sig(
                tcx, @Nil, Some(transformed_self_ty), &bare_fn_ty.sig,
                |_br| self.fcx.infcx().next_region_var_nb(self.expr.span));
        let transformed_self_ty = opt_transformed_self_ty.get();
        let fty = ty::mk_bare_fn(tcx, ty::BareFnTy {sig: fn_sig, ..bare_fn_ty});
        debug!("after replacing bound regions, fty=%s", self.ty_to_str(fty));

        let self_mode = get_mode_from_explicit_self(candidate.method_ty.explicit_self);

        // Check that the receiver's type is a subtype of the actual,
        // expected type. This can fail if the self type doesn't line
        // up; e.g., `self_ty` is `@Foo` and we are calling an method
        // on `Foo` with a `~self` declaration.
        match self.fcx.mk_subty(false, self.self_expr.span,
                                adj_self_ty, transformed_self_ty) {
            Ok(_) => {}
            Err(e) => {
                return Err(ExpectedFound(transformed_self_ty, adj_self_ty, e));
            }
        }

        self.fcx.write_ty(self.callee_id, fty);
        self.fcx.write_substs(self.callee_id, all_substs);
        Ok(method_map_entry {
            self_ty: transformed_self_ty,
            self_mode: self_mode,
            explicit_self: candidate.method_ty.explicit_self,
            origin: candidate.origin,
        })
    }

    fn enforce_object_limitations(&self,
                                  method_fty: ty::t,
                                  candidate: &Candidate)
                                  -> Result<(), SearchError>
    {
        /*!
         * There are some limitations to calling functions through an
         * object, because (a) the self type is not known
         * (that's the whole point of a trait instance, after all, to
         * obscure the self type) and (b) the call must go through a
         * vtable and hence cannot be monomorphized.
         */

        match candidate.origin {
            method_static(*) | method_param(*) |
            method_self(*) | method_super(*) => {
                return Ok(()); // not a call to a trait instance
            }
            method_trait(*) => {}
        }

        if ty::type_has_self(method_fty) { // reason (a) above
            return Err(ObjectMethodReferencingSelf);
        }

        if candidate.method_ty.generics.has_type_params() { // reason (b) above
            return Err(ObjectMethodGeneric);
        }

        return Ok(());
    }

    fn enforce_drop_trait_limitations(&self,
                                      candidate: &Candidate)
                                      -> Result<(), SearchError> {
        /*!
         * Check that no code calls the finalize method explicitly.
         */

        let bad = match candidate.origin {
            method_static(method_id) | method_self(method_id, _)
                | method_super(method_id, _) => {
                self.tcx().destructors.contains(&method_id)
            }
            method_param(method_param { trait_id: trait_id, _ }) |
            method_trait(trait_id, _) => {
                self.tcx().destructor_for_type.contains_key(&trait_id)
            }
        };

        if bad {
            return Err(DropTraitMethod);
        } else {
            return Ok(());
        }
    }

    fn construct_transformed_self_ty_for_object(&self,
                                                trait_def_id: ast::def_id,
                                                candidate: &Candidate) -> ty::t
    {
        /*!
         * This is a bit tricky. We have a match against a trait method
         * being invoked on an object, and we want to generate the
         * self-type. As an example, consider a trait
         *
         *     trait Foo {
         *         fn r_method<'a>(&'a self);
         *         fn m_method(@mut self);
         *     }
         *
         * Now, assuming that `r_method` is being called, we want the
         * result to be `&'a Foo`. Assuming that `m_method` is being
         * called, we want the result to be `@mut Foo`. Of course,
         * this transformation has already been done as part of
         * `candidate.method_ty.transformed_self_ty`, but there the
         * type is expressed in terms of `Self` (i.e., `&'a Self`, `@mut Self`).
         * Because objects are not standalone types, we can't just substitute
         * `s/Self/Foo/`, so we must instead perform this kind of hokey
         * match below.
         */

        let substs = ty::substs {self_r: candidate.rcvr_substs.self_r,
                                 self_ty: None,
                                 tps: candidate.rcvr_substs.tps.clone()};
        match candidate.method_ty.explicit_self {
            r @ ast::sty_static | r @ ast::sty_value => {
                // Should have reported an error in the earlier stages
                self.tcx.sess.span_bug(
                    self.expr.span,
                    fmt!("object method with illegal explicit self %?", r));
            }
            ast::sty_region(*) | ast::sty_box(*) | ast::sty_uniq(*) => {
                let transformed_self_ty =
                    candidate.method_ty.transformed_self_ty.get();
                match ty::get(transformed_self_ty).sty {
                    ty::ty_rptr(r, mt) => { // must be sty_region
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, ty::RegionTraitStore(r), mt.mutbl)
                    }
                    ty::ty_box(mt) => { // must be sty_box
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, ty::BoxTraitStore, mt.mutbl)
                    }
                    ty::ty_uniq(mt) => { // must be sty_uniq
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, ty::UniqTraitStore, mt.mutbl)
                    }
                    _ => {
                        self.bug(
                            fmt!("'impossible' transformed_self_ty: %s",
                                 transformed_self_ty.repr(self.tcx())));
                    }
                }
            }
        }
    }
}

// Useful helper function. This is used by both `inherent` and
// `traits` searchers.

pub fn push_candidates_from_impl(lookupcx: &LookupContext,
                                 impl_info: &ty::Impl,
                                 out: &mut ~[Candidate]) {
    // Search for a method with the required name.
    let idx = {
        match impl_info.methods.position(|m| m.ident == lookupcx.m_name) {
            Some(idx) => idx,
            None => { return; } // No method with the right name.
        }
    };
    let method = ty::method(lookupcx.tcx(), impl_info.methods[idx].did);

    // Obtain a substitution `impl_substs` with fresh type
    // variables for each of the impl's type parameters.
    let location_info = &vtable::location_info_for_expr(lookupcx.self_expr);
    let vcx = vtable::VtableContext {
        ccx: lookupcx.fcx.ccx,
        infcx: lookupcx.fcx.infcx()
    };
    let ty::ty_param_substs_and_ty {
        substs: impl_substs,
        ty: _
    } = check::impl_self_ty(&vcx, location_info, impl_info.did);

    // Push the result.
    out.push(Candidate {
        rcvr_substs: impl_substs,
        method_ty: method,
        origin: method_static(method.def_id)
    });
}

impl Repr for Candidate {
    fn repr(&self, tcx: ty::ctxt) -> ~str {
        fmt!("Candidate(rcvr_substs=%s, method_ty=%s, origin=%s)",
             self.rcvr_substs.repr(tcx),
             self.method_ty.repr(tcx),
             self.origin.repr(tcx))
    }
}
