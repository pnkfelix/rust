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

use core::prelude::*;

use mc = middle::mem_categorization;
use middle::ty;
use middle::borrowck::*;
use middle::borrowck::compute_loans::*;
use util::common::indenter;

use core::result::{Err, Ok, Result};
use syntax::ast::{m_const, m_imm, m_mutbl};
use syntax::ast;

impl Reserve for ComputeLoansContext {
    fn reserve(&self,
               cmt: mc::cmt,
               loan_region: ty::Region,
               reason: ReserveReason) -> BckResult<LoansOrRoot>
    {
        debug!("mutate(cmt=%s, loan_region=%?, reason=%?)",
               self.bccx.cmt_to_repr(cmt), loan_region, reason);
        let _i = indenter();

        match cmt.cat {
            mc::cat_local(local_id) |
            mc::cat_arg(local_id, ast::by_copy) |
            mc::cat_self(local_id) => {
                reserve_variable(self, cmt, loan_region, local_id)
            }

            mc::cat_stack_upvar(cmt_base) => {
                self.reserve(cmt_base, loan_region, reason)
            }

            mc::cat_interior(cmt_base, f @ mc::interior_field(*)) |
            mc::cat_interior(cmt_base, f @ mc::interior_index(*)) => {
                reserve_owned_content(self, cmt, loan_region, reason,
                                      cmt_base, LpInterior(f))
            }

            mc::cat_interior(cmt_base, f @ mc::interior_tuple) |
            mc::cat_interior(cmt_base, f @ mc::interior_anon_field) |
            mc::cat_interior(cmt_base, f @ mc::interior_variant(*)) => {
                reserve_owned_content(self, cmt, loan_region, reason,
                                      cmt_base, LpInterior(f))
            }

            mc::cat_deref(cmt_base, _, mc::uniq_ptr(*)) => {
                reserve_owned_content(self, cmt, loan_region, reason,
                                      cmt_base, LpDeref)
            }

            mc::cat_deref(cmt_base, _, mc::region_ptr(m, _)) => {
                reserve_borrowed_ptr(self, cmt, loan_region, reason,
                                     cmt_base, m)
            }

            mc::cat_deref(_, _, mc::unsafe_ptr) => {
                Ok(Safe)
            }

            mc::cat_rvalue => {
                // Rvalues are immutable temporaries.  They are not
                // directly referencable by users and hence are not
                // aliasable.
                Ok(Safe)
            }

            mc::cat_copied_upvar(_) => {
                // Copied upvars are aliasable because of the
                // possibility of recursive calls
                reserve_aliasable(self, cmt, reason)
            }

            mc::cat_discr(cmt_base, match_id) => {
                self.with_discr(match_id,
                                |c| c.reserve(cmt_base, loan_region, reason))
            }

            mc::cat_static_item |
            mc::cat_implicit_self |
            mc::cat_arg(_, ast::by_ref) |
            mc::cat_arg(_, ast::by_val) |
            mc::cat_deref(_, _, mc::gc_ptr(*)) => {
                reserve_aliasable(self, cmt, reason)
            }
        }
    }
}

fn reserve_variable(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    local_id: ast::node_id) -> BckResult<LoansOrRoot>
{
    // See rule Reserve-Variable in doc.rs
    self.loan_variable_without_checking_scope(
        cmt, loan_region, Total, ReserveLoan, local_id)
}

fn reserve_owned_content(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    reason: ReserveReason,
    cmt_base: mc::cmt,
    lp_elem: LoanPathElem) -> BckResult<LoansOrRoot>
{
    // See rule Reserve-Field in doc.rs
    let loans = if_ok!(self.reserve(cmt_base, loan_region, reason));
    Ok(self.add_loan(loans, cmt, loan_region, ReserveLoan, Total, lp_elem))
}

fn reserve_borrowed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    reason: ReserveReason,
    cmt_base: mc::cmt,
    pointer_mutbl: ast::mutability) -> BckResult<LoansOrRoot>
{
    match pointer_mutbl {
        m_imm | m_const => {
            Err(BckError {
                cmt: cmt,
                span: self.span,
                code: err_cannot_reserve_aliasable_value(reason)
            })
        }

        m_mutbl => {
            // See rules Reserve-Mut-Borrowed-Ptr in doc.rs
            let loans = if_ok!(self.reserve(cmt_base, loan_region,
                                            reason));
            Ok(self.add_loan(loans, cmt, loan_region, ReserveLoan, Total,
                             LpDeref))
        }
    }
}

fn reserve_aliasable(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    reason: ReserveReason) -> BckResult<LoansOrRoot>
{
    Err(BckError {
        cmt: cmt,
        span: self.span,
        code: err_cannot_reserve_aliasable_value(reason)
    })
}