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

This module defines the function compute_loans, which computes the set
of loans needed to guarantee that a borrow is safe.  See the comment
in borrowck/mod.rs for more information.

*/

use mc = middle::mem_categorization;
use middle::ty;
use middle::borrowck::*;
use middle::borrowck::compute_loans::*;
use util::common::indenter;

use core::result::{Err, Ok};
use syntax::ast::{m_const, m_imm, m_mutbl};
use syntax::ast;

impl Freeze for ComputeLoansContext {
    fn freeze(&self,
              cmt: mc::cmt,
              loan_region: ty::Region,
              totality: PartialTotal) -> BckResult<LoansOrRoot>
    {
        debug!("freeze(cmt=%s, loan_region=%?, totality=%?)",
               cmt.repr(self.tcx()), loan_region, totality);
        let _i = indenter();

        match cmt.cat {
            mc::cat_local(local_id) |
            mc::cat_arg(local_id, _) |
            mc::cat_self(local_id) => {
                freeze_variable(self, cmt, loan_region, totality, local_id)
            }

            mc::cat_interior(cmt_base, f @ mc::interior_field(_, m)) |
            mc::cat_interior(cmt_base, f @ mc::interior_index(_, m)) => {
                freeze_owned_content(self, cmt, loan_region, totality,
                                     cmt_base, m, LpInterior(f))
            }

            mc::cat_interior(cmt_base, f @ mc::interior_tuple) |
            mc::cat_interior(cmt_base, f @ mc::interior_anon_field) |
            mc::cat_interior(cmt_base, f @ mc::interior_variant(_)) => {
                freeze_owned_content(self, cmt, loan_region, totality,
                                     cmt_base, m_imm, LpInterior(f))
            }

            mc::cat_deref(cmt_base, _, mc::uniq_ptr(m)) => {
                freeze_owned_content(self, cmt, loan_region, totality,
                                     cmt_base, m, LpDeref)
            }

            mc::cat_deref(cmt_base, _, mc::region_ptr(m, r)) => {
                freeze_borrowed_ptr(self, cmt, loan_region, totality,
                                    cmt_base, m, r)
            }

            mc::cat_deref(cmt_base, derefs, mc::gc_ptr(m)) => {
                freeze_managed_ptr(self, cmt, loan_region, totality,
                                   cmt_base, derefs, m)
            }

            mc::cat_deref(_, _, mc::unsafe_ptr) => {
                // Ignore mutability of `*T` pointers and just assume
                // the user knows what they are doing.
                Ok(Safe)
            }

            mc::cat_static_item => {
                Ok(Safe)
            }

            mc::cat_implicit_self | mc::cat_copied_upvar(_) => {
                self.alias_or_freeze_item_scope(cmt, loan_region)
            }

            mc::cat_rvalue => {
                self.alias_or_freeze_rvalue(cmt, loan_region)
            }

            mc::cat_stack_upvar(cmt) => {
                self.freeze(cmt, loan_region, totality)
            }

            mc::cat_discr(cmt_base, match_id) => {
                self.with_discr(match_id,
                                |c| c.freeze(cmt_base, loan_region, totality))
            }
        }
    }
}

fn freeze_variable(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    totality: PartialTotal,
    local_id: ast::node_id) -> BckResult<LoansOrRoot>
{
    // See rule Freeze-Variable in doc.rs
    if_ok!(self.check_cmt_scope(cmt, loan_region));
    self.loan_variable(cmt, loan_region, MutLoan(m_imm, totality), local_id)
}

fn freeze_owned_content(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    totality: PartialTotal,
    cmt_base: mc::cmt,
    content_mutbl: ast::mutability,
    lp_elem: LoanPathElem) -> BckResult<LoansOrRoot>
{
    match content_mutbl {
        m_imm => {
            // See rules Freeze-Field, Freeze-Owned-Ptr in doc.rs
            let loans = if_ok!(self.freeze(cmt_base, loan_region, Partial));
            Ok(self.add_loan(loans, cmt, loan_region,
                             MutLoan(m_imm, totality), lp_elem))
        }

        m_const | m_mutbl => {
            // Declared as const or mutable.  This is more complicated, as
            // we have to ensure that the mut field is not found
            // in an aliasable location.  Adapt the approach
            // described as Mutate-Mut-Borrowed-Pointer in doc.rs.

            // FIXME(#5397) --- Mut fields currently unsound
            // match self.reserve(cmt_base, loan_region, ReserveForMutField) {
            //     Ok(loans) => {
            //         Ok(self.add_loan(loans, cmt, loan_region,
            //                          MutLoan(m_imm, totality), lp_elem))
            //     }
            //
            //     Err(e) => {
            //         Err(e)
            //     }
            // }

            Ok(Safe)
        }
    }
}

fn freeze_borrowed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    totality: PartialTotal,
    cmt_base: mc::cmt,
    pointer_mutbl: ast::mutability,
    pointer_region: ty::Region) -> BckResult<LoansOrRoot>
{
    match pointer_mutbl {
        m_imm => {
            // See rule Freeze-Imm-Borrowck-Ptr in doc.rs
            if_ok!(self.check_scope(cmt, loan_region, pointer_region));
            Ok(Safe)
        }

        m_const => {
            Err(BckError {cmt: cmt,
                          span: self.span,
                          code: err_mutbl(m_imm)})
        }

        m_mutbl => {
            // See rule Freeze-Mut-Borrowck-Ptr in doc.rs
            self.mutate_or_freeze_mut_borrowed_ptr(
                cmt, loan_region, cmt_base, pointer_mutbl,
                pointer_region, MutLoan(m_imm, totality))
        }
    }
}

fn freeze_managed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    totality: PartialTotal,
    cmt_base: mc::cmt,
    derefs: uint,
    pointer_mutbl: ast::mutability) -> BckResult<LoansOrRoot>
{
    match pointer_mutbl {
        m_imm => {
            self.root_managed_ptr(
                cmt, loan_region, cmt_base, derefs)
        }

        m_const => {
            Err(BckError {cmt: cmt,
                          span: self.span,
                          code: err_mutbl(m_mutbl)})
        }

        m_mutbl => {
            // See rule Freeze-Mut-Managed-Ptr in doc.rs
            self.mutate_or_freeze_mut_managed_ptr(
                cmt, loan_region, DynaImm, cmt_base,
                derefs, pointer_mutbl)
        }
    }
}