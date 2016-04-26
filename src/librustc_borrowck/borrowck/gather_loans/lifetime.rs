// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module implements the check that the lifetime of a borrow
//! does not exceed the lifetime of the value being borrowed.

use borrowck::*;
use rustc::hir;
use rustc::middle::expr_use_visitor as euv;
use rustc::middle::mem_categorization as mc;
use rustc::middle::mem_categorization::Categorization;
use rustc::middle::region;
use rustc::ty;

use syntax::ast;
use syntax::codemap::Span;

type R = Result<(),()>;

pub fn guarantee_lifetime<'a, 'tcx>(bccx: &BorrowckCtxt<'a, 'tcx>,
                                    item_scope: region::CodeExtent,
                                    span: Span,
                                    cause: euv::LoanCause,
                                    cmt: mc::cmt<'tcx>,
                                    loan_region: ty::Region,
                                    _: ty::BorrowKind)
                                    -> Result<(),()> {
    //! Reports error if `loan_region` is larger than S
    //! where S is `item_scope` if `cmt` is an upvar,
    //! and is scope of `cmt` otherwise.
    debug!("guarantee_lifetime(cmt={:?}, loan_region={:?})",
           cmt, loan_region);
    let ctxt = GuaranteeLifetimeContext {bccx: bccx,
                                         item_scope: item_scope,
                                         span: span,
                                         cause: cause,
                                         loan_region: loan_region,
                                         cmt_original: cmt.clone()};
    ctxt.check(&cmt, None)
}

///////////////////////////////////////////////////////////////////////////
// Private

struct GuaranteeLifetimeContext<'a, 'tcx: 'a> {
    bccx: &'a BorrowckCtxt<'a, 'tcx>,

    // the scope of the function body for the enclosing item
    item_scope: region::CodeExtent,

    span: Span,
    cause: euv::LoanCause,
    loan_region: ty::Region,
    cmt_original: mc::cmt<'tcx>
}

enum ScopeConstraint<'tcx> {
    /// This constraint arises when the guaranator for the data does
    /// not live long enough. For example, given `x: &'a &'b &'c T`,
    /// `**x` (which has type &'c T`) can only be borrowed for at most
    /// the lifetime `'b`.
    ShortLivedShallowGuarantor { max_scope: ty::Region },

    /// This scope constraint arises when re-borrowing via a `&mut`
    /// reference to the borrowed data where the object owning the
    /// `&mut` has a destructor.
    DestructorMutBaseGuarantor {
        max_scope: ty::Region,
        base_guarantor: mc::cmt<'tcx>,
        dtor_ty: ty::Ty<'tcx>,
    }
}

impl<'tcx> ScopeConstraint<'tcx> {
    fn max_scope(&self) -> ty::Region {
        match *self {
            ScopeConstraint::ShortLivedShallowGuarantor { max_scope } => max_scope,
            ScopeConstraint::DestructorMutBaseGuarantor { max_scope, .. } => max_scope,
        }
    }
}

impl<'a, 'tcx> GuaranteeLifetimeContext<'a, 'tcx> {

    fn check(&self, cmt: &mc::cmt<'tcx>, discr_scope: Option<ast::NodeId>) -> R {
        //! Main routine. Walks down `cmt` until we find the
        //! "guarantor".  Reports an error if `self.loan_region` is
        //! larger than scope of `cmt`.
        debug!("guarantee_lifetime.check(cmt={:?}, loan_region={:?})",
               cmt,
               self.loan_region);

        match cmt.cat {
            Categorization::Rvalue(..) |
            Categorization::Local(..) |                         // L-Local
            Categorization::Upvar(..) => {
                let constraint = ScopeConstraint::ShortLivedShallowGuarantor {
                    max_scope: self.scope(cmt),
                };
                self.check_scope(constraint)
            }

            Categorization::Deref(_, _, mc::BorrowedPtr(..)) |  // L-Deref-Borrowed
            Categorization::Deref(_, _, mc::Implicit(..)) |
            Categorization::Deref(_, _, mc::UnsafePtr(..)) => {
                let tcx = self.bccx.tcx;

                // Issue #31567: if guarantor has a destructor, then
                // that destructor may access guarantor's borrowed
                // content. Thus must either (1.) restrict lifetime of
                // caller's borrow, or (2.) ensure that neither borrow
                // is an unaliasable borrow.
                //
                // Note that checking (2.) reduces to just ensuring
                // that the guarantor's borrow is aliasable, since one
                // cannot safely turn an aliasable borrow into an
                // unique one.

                match mut_guarantor_with_drop_impl(tcx, cmt) {
                    Some((base_guarantor, dtor_ty)) => {
                        // case (1.)
                        let scope = self.scope(&base_guarantor);
                        let constraint = ScopeConstraint::DestructorMutBaseGuarantor {
                            max_scope: scope,
                            base_guarantor: base_guarantor,
                            dtor_ty: dtor_ty,
                        };
                        self.check_scope(constraint)?;
                    }
                    None => {
                        // case (2.), satisfied by analysis in
                        // mut_guarantor_with_drop_impl.
                    }
                }

                let constraint = ScopeConstraint::ShortLivedShallowGuarantor {
                    max_scope: self.scope(cmt),
                };
                self.check_scope(constraint)
            }

            Categorization::StaticItem => {
                Ok(())
            }

            Categorization::Downcast(ref base, _) |
            Categorization::Deref(ref base, _, mc::Unique) |     // L-Deref-Send
            Categorization::Interior(ref base, _) => {             // L-Field
                self.check(base, discr_scope)
            }
        }
    }

    fn check_scope(&self, constraint: ScopeConstraint<'tcx>) -> R {
        //! Reports an error if `loan_region` is larger than `constraint.max_scope`

        let max_scope = constraint.max_scope();
        let ret = if !self.bccx.is_subregion_of(self.loan_region, max_scope) {
            match constraint {
                ScopeConstraint::ShortLivedShallowGuarantor { .. } =>
                    Err(self.report_error(err_out_of_scope(max_scope, self.loan_region))),
                ScopeConstraint::DestructorMutBaseGuarantor {
                    base_guarantor, dtor_ty, .. } => {
                    self.report_error(err_out_of_scope_dtor {
                        superscope: max_scope,
                        subscope: self.loan_region,
                        owner: base_guarantor.clone(),
                        dtor_ty: dtor_ty,
                    });
                    Ok(())
                }
            }
        } else {
            Ok(())
        };
        debug!("check_scope: {:?} {:?}: {:?}", self.loan_region, max_scope, ret);
        ret
    }

    fn scope(&self, cmt: &mc::cmt) -> ty::Region {
        //! Returns the maximal region scope for the which the
        //! lvalue `cmt` is guaranteed to be valid without any
        //! rooting etc, and presuming `cmt` is not mutated.

        match cmt.cat {
            Categorization::Rvalue(temp_scope) => {
                temp_scope
            }
            Categorization::Upvar(..) => {
                ty::ReScope(self.item_scope)
            }
            Categorization::StaticItem => {
                ty::ReStatic
            }
            Categorization::Local(local_id) => {
                ty::ReScope(self.bccx.tcx.region_maps.var_scope(local_id))
            }
            Categorization::Deref(_, _, mc::UnsafePtr(..)) => {
                ty::ReStatic
            }
            Categorization::Deref(_, _, mc::BorrowedPtr(_, r)) |
            Categorization::Deref(_, _, mc::Implicit(_, r)) => {
                r
            }
            Categorization::Downcast(ref cmt, _) |
            Categorization::Deref(ref cmt, _, mc::Unique) |
            Categorization::Interior(ref cmt, _) => {
                self.scope(cmt)
            }
        }
    }

    fn report_error(&self, code: bckerr_code<'tcx>) {
        self.bccx.report(BckError { cmt: self.cmt_original.clone(),
                                    span: self.span,
                                    cause: BorrowViolation(self.cause),
                                    code: code });
    }
}

fn has_user_defined_dtor<'tcx>(ty: ty::Ty<'tcx>) -> bool
{
    match ty.sty {
        ty::TyEnum(type_def, _) | ty::TyStruct(type_def, _) => {
            type_def.destructor().is_some()
        }
        _ => false,
    }
}

fn mut_guarantor_with_drop_impl<'tcx>(_ctxt: &ty::TyCtxt<'tcx>,
                                      orig_cmt: &mc::cmt<'tcx>)
                                      -> Option<(mc::cmt<'tcx>, ty::Ty<'tcx>)>
{
    // Someone is borrowing `orig_cmt`. Our goal is to ensure that the
    // lifetime of the borrow does not overlap the execution of any
    // destructors that have `&mut` access to the borrowed data.
    //
    // This is a little tricky to get right. Consider a case like
    // this: given `z: &'a mut D(&'b mut u8, u8)`, with a (user-
    // defined) `impl Drop for D`.
    //
    // Is this: `&*((*z).0): &'b u8` allowed?
    //
    // How about this: `&mut *((*z).0): &'b u8`?
    //
    // The answer: Neither is allowed, because we only know that the
    // destructor won't run until sometime after `'a` expires.
    //
    // (There are other pre-existing checks, like the RESTRICTIONS
    // clause R-Deref-Imm-Borrowed, that handle similar cases. So it
    // is important that we stay focused on the problem at hand:
    // identifying all potential future-scheduled destructor
    // invocations with `&mut` access to data being borrowed here.)

    // First, some expository examples. We will assume that `x` is a
    // local variable of some type `X` and associated scope lifetime
    // `'x`. The structure of `X` will be implied from context; any
    // fields of the structure, `.f1`, `.f2`, etc have corresponding
    // types `F1`, `F2`, etc.
    //
    // All examples will make explicit the borrow being requested,
    // using type ascription to declare the lifetime of the requested
    // borrow.
    //
    // `&x: &'lt X` is always okay with this check: a borrow of a
    // local will always expire before the execution of that local's
    // destructor.
    //
    // `&*x: &'lt _` is ok (assuming `X = &'y mut _` or `X = &'y _`):
    // the borrowed data must outlive `'y`, and `'y: 'lt`; thus there
    // is no relevant destructor that will run before `'lt` expires.
    //
    // `&x.f1: &'lt F1` ok if !(X:Drop) or 'lt < 'x.
    //
    // `&*(x.f1): &'lt _` ok if !(X:Drop) or 'lt < 'x or F1 != `&mut _`.
    //
    // Note that the conditions here are the combination of the same
    // set of conditions as the previous case, plus an additional
    // escape clause based on the structure of `F1`. The type `F1` has
    // to be *some* reference type (since we are dereferencing it),
    // and the unsafety we are checking for is only exposed if `F1` is
    // a `&mut _`.
    // 
    // `&x.f1.f2: &'lt X` ok if (!(X:Drop) and !(F1:Drop)) or 'lt < 'x.
    //
    // One last interesting example:
    //
    // `&(*(x.f1.f2)).f3: &'lt F3` ok if (!(X:Drop) and !(F1:Drop)) or
    // 'lt < 'x or `F2 != &'y mut _`.
    //
    // This last example is interesting because it illustrates that we
    // need not care about whether `F3:Drop` when we only access it as
    // a field off of a dereference: we know `x.f1.f2` is a reference
    // to some structure holding the `.f3: F3`, which means the
    // destructor for `F3` will never run. We also know that `F2` has
    // no destructor (since it must be of reference type). However,
    // *either* of the types `X` or `F1` could have a destructor that
    // could access the mutable state.
    //
    // In other words, as we decend the structure of the cmt making
    // our way to its foundational owner, each time that we encounter
    // a `Deref`, we can disregard any destructor-laden types that we
    // encountered on our way here.

    // From the above examples, I generalize as follows:
    //
    // /// Returns min. bound on how long before a dtor could access
    // /// the borrowed data. If None then no such dtor exists.
    //
    // fn base_guarantor(LV) -> Option<Lifetime> {
    //   fn recur(LV, found_drop: bool) -> Option<Lifetime> {
    //     match LV {
    //       X => if found_drop { Some(SCOPE(X)) } else { None }
    //       *LV' => if TYPE(LV) != `&mut _` { None } else { recur(LV', false) },
    //       LV'.f => recur(LV', found_drop || TYPE(LV'): Drop),
    //     }
    //   }
    //   recur(LV, false)
    // }
    //
    // However, the above is an ad-hoc generalization from the
    // examples; I have not yet really proven to myself that this is
    // fundamentally correct.
    
    let mut cmt = orig_cmt;
    let mut found_drop: Option<ty::Ty<'tcx>> = None;
    let base;
    loop {
        debug!("mut_guarantor_with_drop_impl cmt: {:?} found_drop: {:?}",
               cmt, found_drop);

        // Note on upvar: If base cmt is upvar reference, then its ty
        // is not reliable (mem_categorization just plugs in `TyErr`).
        // That is why I am breaking out in those cases below.
        match cmt.cat {
            Categorization::Rvalue(..) |
            Categorization::StaticItem |
            Categorization::Local(..)  |
            Categorization::Upvar(..) => {
                base = cmt.clone();
                break;
            }

            Categorization::Interior(ref b, _) => {
                if let Categorization::Upvar(..) = b.cat {
                    // see Note on upvar above.
                    base = cmt.clone();
                    break;
                }

                // accumulate potential destructors on LV.f
                if found_drop.is_none() && has_user_defined_dtor(b.ty) {
                    found_drop = Some(b.ty);
                }
                cmt = b;
            }

            Categorization::Downcast(ref b, _) |
            Categorization::Deref(ref b, _, mc::UnsafePtr(..)) |
            Categorization::Deref(ref b, _, mc::Unique) => {
                if let Categorization::Upvar(..) = b.cat {
                    // see Note on upvar above.
                    base = cmt.clone();
                    break;
                }
                cmt = b;
            }

            Categorization::Deref(ref b, _, mc::BorrowedPtr(..)) |
            Categorization::Deref(ref b, _, mc::Implicit(..)) => {
                if let Categorization::Upvar(..) = b.cat {
                    // see Note on upvar above.
                    base = cmt.clone();
                    break;
                }
                cmt = b;

                // reset potential destructors on *LV.
                found_drop = None;

                if let ty::TyRef(_, ty::TypeAndMut { ty: _, mutbl }) = b.ty.sty
                {
                    if mutbl != hir::MutMutable { return None; }
                }
            }
        };
    }

    let ret = if let Some(dtor_ty) = found_drop {
        Some((base, dtor_ty))
    } else {
        None
    };
    debug!("mut_guarantor_with_drop_impl cmt: {:?} => {:?}", orig_cmt, ret);
    ret
}
