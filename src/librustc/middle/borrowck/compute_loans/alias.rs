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

impl Alias for ComputeLoansContext {
    fn alias(&self,
             cmt: mc::cmt,
             loan_region: ty::Region,
             pt: PartialTotal) -> BckResult<LoansOrRoot>
    {
        debug!("mutate(cmt=%s, loan_region=%?, pt=%?)",
               self.bccx.cmt_to_repr(cmt), loan_region, pt);
        let _i = indenter();

        match cmt.cat {
            mc::cat_local(local_id) |
            mc::cat_arg(local_id, _) |
            mc::cat_self(local_id) => {
                alias_variable(self, cmt, loan_region, pt, local_id)
            }

            mc::cat_interior(cmt_base, f @ mc::interior_field(*)) |
            mc::cat_interior(cmt_base, f @ mc::interior_index(*)) => {
                alias_owned_interior(self, cmt, loan_region, pt,
                                     cmt_base, LpInterior(f))
            }

            mc::cat_interior(cmt_base, f @ mc::interior_tuple) |
            mc::cat_interior(cmt_base, f @ mc::interior_anon_field) |
            mc::cat_interior(cmt_base, f @ mc::interior_variant(_)) => {
                alias_owned_interior(self, cmt, loan_region, pt,
                                      cmt_base, LpInterior(f))
            }

            mc::cat_deref(cmt_base, _, mc::uniq_ptr(_)) => {
                alias_owned_pointer(self, cmt, loan_region, pt, cmt_base)
            }

            mc::cat_deref(_, _, mc::region_ptr(_, r)) => {
                alias_borrowed_ptr(self, cmt, loan_region, pt, r)
            }

            mc::cat_deref(cmt_base, derefs, mc::gc_ptr(*)) => {
                alias_managed_ptr(self, cmt, loan_region,
                                  cmt_base, derefs)
            }

            mc::cat_deref(_, _, mc::unsafe_ptr) => {
                Ok(Safe)
            }

            mc::cat_discr(cmt_base, match_id) => {
                self.with_discr(match_id,
                                |c| c.alias(cmt_base, loan_region, pt))
            }

            mc::cat_static_item => {
                Ok(Safe)
            }

            mc::cat_implicit_self | mc::cat_copied_upvar(_) => {
                self.alias_or_freeze_item_scope(cmt, loan_region, pt)
            }

            mc::cat_rvalue => {
                self.alias_or_freeze_rvalue(cmt, loan_region, pt)
            }

            mc::cat_stack_upvar(cmt) => {
                self.freeze(cmt, loan_region, pt)
            }
        }
    }
}

fn alias_variable(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    local_id: ast::node_id) -> BckResult<LoansOrRoot>
{
    // See rule Alias-Variable in doc.rs
    self.loan_variable(cmt, loan_region, pt, MutLoan(ast::m_const), local_id)
}

fn alias_owned_interior(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    cmt_base: mc::cmt,
    lp_elem: LoanPathElem) -> BckResult<LoansOrRoot>
{
    // See rule Alias-Field in doc.rs
    let loans = if_ok!(self.alias(cmt_base, loan_region, Partial));
    Ok(self.add_loan(loans, cmt, loan_region, MutLoan(ast::m_const), pt,
                     lp_elem))
}

fn alias_owned_pointer(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    cmt_base: mc::cmt) -> BckResult<LoansOrRoot>
{
    // See rule Alias-Owned-Pointer in doc.rs
    let loans = if_ok!(self.freeze(cmt_base, loan_region, Partial));
    Ok(self.add_loan(loans, cmt, loan_region, MutLoan(ast::m_const), pt,
                     LpDeref))
}

fn alias_borrowed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    _pt: PartialTotal,
    pointer_region: ty::Region) -> BckResult<LoansOrRoot>
{
    // See rule Alias-Borrowed-Pointer in doc.rs
    if_ok!(self.check_scope(cmt, loan_region, pointer_region));
    Ok(Safe)
}

fn alias_managed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    cmt_base: mc::cmt,
    derefs: uint) -> BckResult<LoansOrRoot>
{
    // See rules Alias-Managed-Pointer-{1,2} in doc.rs
    self.root_managed_ptr(cmt, loan_region, cmt_base, derefs)
}