// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::typeck::check;
use middle::subst::Subst;

trait MethodSearch {
    fn push_candidates(&mut self, rcvr_ty: ty::t, out: &mut [Candidate]);
}

struct Candidate {
    rcvr_match_condition: RcvrMatchCondition,
    rcvr_substs: ty::substs,
    method_ty: @ty::Method,
    origin: method_origin,
}

enum SearchError {
    StaticMethodCalled,
    NotManaged,
    NotOwned,
    ExpectedFound(ty::t, ty::t),
    NoMethodFound,
}

type SearchResult = Result<method_map_entry, SearchError>;

impl LookupContext {
    pub fn do_search<M:MethodSearch>(&mut self,
                                     rcvr_ty: ty::t,
                                     search: &mut M)
                                     -> SearchResult {
        let mut dids = ~[];
        let mut rcvr_tys = ~[rcvr_ty];
        let mut candidates = ~[];

        loop {
            search.push_candidates(*rcvr_tys.last(), &mut candidates);
            if !candidates.is_empty() {
                return self.evaluate_candidates(rcvr_tys, candidates);
            }

            match self.deref(*rcvr_tys.last(), &mut dids) {
                None => {
                    return self.evaluate_slice(*rcvr_tys.last());
                }
                Some(t) => {
                    rcvr_tys.push(t);
                }
            }
        }
    }

    fn deref(&mut self, ty: ty::t, dids: &mut [ast::def_id]) {
        match ty::get(ty).sty {
            ty_enum(did, _) | ty_struct(did, _) => {
                // Watch out for newtype'd enums like "struct
                // T(@T)", which could induce an infinite
                // loop. See discussion in
                // typeck::check::do_autoderef().
                if dids.contains(&did) {
                    return None;
                }
                dids.push(did);
            }
            _ => {}
        }

        match ty::deref(self.tcx(), rcvr_ty, false) {
            None => {
                return None;
            }
            Some(t) => {
                Some(check::structurally_resolved_type(self.fcx,
                                                       self.self_expr.span,
                                                       t.ty))
            }
        }
    }

    fn evaluate_candidates(&mut self,
                           rcvr_tys: &[ty::t],
                           candidates: ~[Candidate])
                           -> SearchResult {
        assert!(!candidates.is_empty());

        if candidates.len() > 1 {
            // report ambig error
            XXX
        }

        let candidate = candidates.pop();
        self.evaluate_candidate(rcvr_tys, candidate)
    }

    fn evaluate_candidate(&mut self,
                          rcvr_tys: &[ty::t],
                          candidate: Candidate)
                          -> SearchResult {
        assert!(!rcvr_tys.is_empty());
        let autoderefs = rcvr_tys.len() - 1;
        match candidate.explicit_self {
            sty_static => {
                Err(StaticMethodCalled)
            }

            sty_value => {
                self.test_candidate_type(
                    rcvr_tys[0],
                    candidate,
                    ty::AutoDerefRef(ty::AutoDerefRef {
                        autoderefs: autoderefs,
                        autoref: None}))
            }

            sty_region(Option<@Lifetime>, m) => {
                let region = self.infcx().next_region_var_nb(self.expr.span);
                let rptr_ty = ty::mk_rptr(tcx, region,
                                          ty::mt {ty: rcvr_tys[0], mutbl: m});
                self.test_candidate_type(
                    rptr_ty,
                    candidate,
                    ty::AutoDerefRef(ty::AutoDerefRef {
                        autoderefs: autoderefs,
                        autoref: AutoPtr(region, m)}))
            }

            sty_box(_) => {
                if rcvr_tys.len() > 1 {
                    self.test_candidate_type(
                        rcvr_tys[1],
                        candidate,
                        ty::AutoDerefRef(ty::AutoDerefRef {
                            autoderefs: autoderefs - 1,
                            autoref: None}))
                } else {
                    NotManaged
                }
            }

            sty_uniq(_) => {
                if rcvr_tys.len() > 1 {
                    self.test_candidate_type(
                        rcvr_tys[1],
                        candidate,
                        ty::AutoDerefRef(ty::AutoDerefRef {
                            autoderefs: autoderefs - 1,
                            autoref: None}))
                } else {
                    NotOwned
                }
            }
        }
    }

    fn evaluate_slice(&mut self,
                      rcvr_ty: ty::t)
                      -> SearchResult {
        // this method would go away under DST
        let tcx = self.tcx();
        let sty = copy ty::get(self_ty).sty;
        match sty {
            ty_evec(mt, vstore_box) |
            ty_evec(mt, vstore_uniq) |
            ty_evec(mt, vstore_slice(_)) |
            ty_evec(mt, vstore_fixed(_)) => {
                // First try to borrow to a slice
                let entry = self.search_for_some_kind_of_autorefd_method(
                    AutoBorrowVec, autoderefs, [m_const, m_imm, m_mutbl],
                    |m,r| ty::mk_evec(tcx,
                                      ty::mt {ty:mt.ty, mutbl:m},
                                      vstore_slice(r)));

                if entry.is_some() { return entry; }

                // Then try to borrow to a slice *and* borrow a pointer.
                self.search_for_some_kind_of_autorefd_method(
                    AutoBorrowVecRef, autoderefs, [m_const, m_imm, m_mutbl],
                    |m,r| {
                        let slice_ty = ty::mk_evec(tcx,
                                                   ty::mt {ty:mt.ty, mutbl:m},
                                                   vstore_slice(r));
                        // NB: we do not try to autoref to a mutable
                        // pointer. That would be creating a pointer
                        // to a temporary pointer (the borrowed
                        // slice), so any update the callee makes to
                        // it can't be observed.
                        ty::mk_rptr(tcx, r, ty::mt {ty:slice_ty, mutbl:m_imm})
                    })
            }

            ty_estr(vstore_box) |
            ty_estr(vstore_uniq) |
            ty_estr(vstore_fixed(_)) => {
                let entry = self.search_for_some_kind_of_autorefd_method(
                    AutoBorrowVec, autoderefs, [m_imm],
                    |_m,r| ty::mk_estr(tcx, vstore_slice(r)));

                if entry.is_some() { return entry; }

                self.search_for_some_kind_of_autorefd_method(
                    AutoBorrowVecRef, autoderefs, [m_imm],
                    |m,r| {
                        let slice_ty = ty::mk_estr(tcx, vstore_slice(r));
                        ty::mk_rptr(tcx, r, ty::mt {ty:slice_ty, mutbl:m})
                    })
            }

            ty_trait(trt_did, trt_substs, _, _) => {
                // Coerce ~/@/&Trait instances to &Trait.

                self.search_for_some_kind_of_autorefd_method(
                    AutoBorrowObj, autoderefs, [m_const, m_imm, m_mutbl],
                    |trt_mut, reg| {
                        ty::mk_trait(tcx, trt_did, copy trt_substs,
                                     RegionTraitStore(reg), trt_mut)
                    })
            }

            ty_closure(*) => {
                // This case should probably be handled similarly to
                // Trait instances.
                None
            }

            _ => None
        }
    }

    fn test_candidate_type(&mut self,
                           rcvr_ty: ty::t,
                           candidate: Candidate,
                           auto_adj: ty::AutoAdjustment)
                           -> SearchResult {
        let tcx = self.tcx();
        let fty = self.fn_ty_from_origin(&candidate.origin);

        debug!("test_candidate_type(expr=%s, candidate=%s, fty=%s)",
               self.expr.repr(tcx),
               self.cand_to_str(candidate),
               self.ty_to_str(fty));

        self.enforce_object_limitations(fty, candidate);
        self.enforce_drop_trait_limitations(candidate);

        // static methods should never have gotten this far:
        assert!(candidate.method_ty.explicit_self != sty_static);

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
            } else if num_method_tps == 0u {
                tcx.sess.span_err(
                    self.expr.span,
                    "this method does not take type parameters");
                self.fcx.infcx().next_ty_vars(num_method_tps)
            } else if num_supplied_tps != num_method_tps {
                tcx.sess.span_err(
                    self.expr.span,
                    "incorrect number of type \
                     parameters given for this method");
                self.fcx.infcx().next_ty_vars(num_method_tps)
            } else {
                self.supplied_tps.to_vec()
            }
        };

        // Construct the full set of type parameters for the method,
        // which is equal to the class tps + the method tps.
        let all_substs = substs {
            tps: vec::append(/*bad*/copy candidate.rcvr_substs.tps,
                             m_substs),
            ../*bad*/copy candidate.rcvr_substs
        };

        // Compute the method type with type parameters substituted
        debug!("fty=%s all_substs=%s", fty.repr(tcx), all_substs.repr(tcx));
        let fty = fty.subst(tcx, &all_substs);
        debug!("after subst, fty=%s", self.ty_to_str(fty));

        // Replace any bound regions that appear in the function
        // signature with region variables
        let bare_fn_ty = match ty::get(fty).sty {
            ty::ty_bare_fn(ref f) => copy *f,
            ref s => {
                tcx.sess.span_bug(
                    self.expr.span,
                    fmt!("Invoking method with non-bare-fn ty: %?", s));
            }
        };
        let (_, opt_transformed_self_ty, fn_sig) =
            replace_bound_regions_in_fn_sig(
                tcx, @Nil, Some(transformed_self_ty), &bare_fn_ty.sig,
                |_br| self.fcx.infcx().next_region_var_nb(self.expr.span));
        let transformed_self_ty = opt_transformed_self_ty.get();
        let fty = ty::mk_bare_fn(tcx, ty::BareFnTy {sig: fn_sig, ..bare_fn_ty});
        debug!("after replacing bound regions, fty=%s", self.ty_to_str(fty));

        let self_mode = get_mode_from_explicit_self(candidate.method_ty.explicit_self);

        // Check that `self_ty` is a subtype of `rcvr_ty`.
        // This can fail if the self type doesn't line up;
        // e.g., `self_ty` is `@Foo` and we are calling an
        // method on `Foo` with a `~self` declaration.
        match self.fcx.mk_subty(false, self.self_expr.span,
                                rcvr_ty, transformed_self_ty) {
            Ok(_) => {}
            Err(_) => {
                return Err(ExpectedFound(transformed_self_ty, rcvr_ty));
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
                                 tps: copy candidate.rcvr_substs.tps};
        match candidate.method_ty.explicit_self {
            ast::sty_static => {
                self.bug(~"static method for object type receiver");
            }
            ast::sty_value => {
                ty::mk_err() // error reported in `enforce_object_limitations()`
            }
            ast::sty_region(*) | ast::sty_box(*) | ast::sty_uniq(*) => {
                let transformed_self_ty =
                    candidate.method_ty.transformed_self_ty.get();
                match ty::get(transformed_self_ty).sty {
                    ty::ty_rptr(r, mt) => { // must be sty_region
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, RegionTraitStore(r), mt.mutbl)
                    }
                    ty::ty_box(mt) => { // must be sty_box
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, BoxTraitStore, mt.mutbl)
                    }
                    ty::ty_uniq(mt) => { // must be sty_uniq
                        ty::mk_trait(self.tcx(), trait_def_id,
                                     substs, UniqTraitStore, mt.mutbl)
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