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

impl Mutate for ComputeLoansContext {
    fn mutate(&self,
              cmt: mc::cmt,
              loan_region: ty::Region,
              pt: PartialTotal) -> BckResult<LoansOrRoot>
    {
        debug!("mutate(cmt=%s, loan_region=%?, pt=%?)",
               self.bccx.cmt_to_repr(cmt), loan_region, pt);
        let _i = indenter();

        match cmt.cat {
            mc::cat_local(local_id) |
            mc::cat_arg(local_id, ast::by_copy) |
            mc::cat_self(local_id) => {
                mutate_variable(self, cmt, loan_region, pt, local_id)
            }

            mc::cat_interior(cmt_base, f @ mc::interior_field(_, m)) |
            mc::cat_interior(cmt_base, f @ mc::interior_index(_, m)) => {
                mutate_owned_content(self, cmt, loan_region, pt,
                                     cmt_base, m, LpInterior(f))
            }

            mc::cat_interior(cmt_base, f @ mc::interior_tuple) |
            mc::cat_interior(cmt_base, f @ mc::interior_anon_field) |
            mc::cat_interior(cmt_base, f @ mc::interior_variant(_)) => {
                mutate_owned_content(self, cmt, loan_region, pt,
                                     cmt_base, m_imm, LpInterior(f))
            }

            mc::cat_deref(cmt_base, _, mc::uniq_ptr(m)) => {
                mutate_owned_content(self, cmt, loan_region, pt,
                                     cmt_base, m, LpDeref)
            }

            mc::cat_deref(cmt_base, _, mc::region_ptr(m, r)) => {
                mutate_borrowed_ptr(self, cmt, loan_region, pt,
                                    cmt_base, m, r)
            }

            mc::cat_deref(cmt_base, derefs, mc::gc_ptr(m)) => {
                mutate_managed_ptr(self, cmt, loan_region, pt,
                                   cmt_base, derefs, m)
            }

            mc::cat_deref(_, _, mc::unsafe_ptr) => {
                // Only allow mutation of `*mut`, but otherwise be
                // trusting.
                if_ok!(self.check_mutable(cmt));
                Ok(Safe)
            }

            mc::cat_discr(cmt_base, match_id) => {
                self.with_discr(match_id,
                                |c| c.mutate(cmt_base, loan_region, pt))
            }

            mc::cat_stack_upvar(cmt) => {
                self.mutate(cmt, loan_region, pt)
            }

            mc::cat_static_item | mc::cat_rvalue => {
                assert cmt.mutbl.is_immutable();
                Err(BckError {cmt: cmt,
                              code: err_mutbl(m_mutbl)})
            }

            mc::cat_copied_upvar(_) => {
                assert cmt.mutbl.is_immutable();
                Err(BckError {cmt: cmt,
                              code: err_mutbl(m_mutbl)})
            }

            mc::cat_implicit_self |
            mc::cat_arg(_, ast::by_ref) |
            mc::cat_arg(_, ast::by_val) => {
                // These kinds of deprecated implicit references are
                // essentially `&T` pointers in disguise, and hence
                // immutable.
                assert cmt.mutbl.is_immutable();
                Err(BckError {cmt: cmt,
                              code: err_mutbl(m_mutbl)})
            }
        }
    }
}

fn mutate_variable(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    local_id: ast::node_id) -> BckResult<LoansOrRoot>
{
    // See rule Mutate-Variable in doc.rs
    if_ok!(self.check_mutable(cmt));
    self.loan_variable(cmt, loan_region, pt, MutLoan(m_mutbl), local_id)
}

fn mutate_owned_content(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    cmt_base: mc::cmt,
    content_mutbl: ast::mutability,
    lp_elem: LoanPathElem) -> BckResult<LoansOrRoot>
{
    match content_mutbl {
        ast::m_imm => {
            // See rules Mutate-Field, Mutate-Owned-Ptr in doc.rs
            let loans = if_ok!(self.mutate(cmt_base, loan_region, Partial));
            Ok(self.add_loan(loans, cmt, loan_region,
                             MutLoan(m_mutbl), pt, lp_elem))
        }

        ast::m_const => {
            // Declared as const.  Mutation not permitted.
            Err(BckError {cmt: cmt,
                          code: err_mutbl(m_mutbl)})
        }

        m_mutbl => {
            // Declared as mutable.  This is more complicated, as
            // we have to ensure that the mut field is not found
            // in an aliasable location.  Adapt the approach
            // described as Mutate-Mut-Borrowed-Pointer in doc.rs.
            let loans = if_ok!(self.reserve(cmt_base, loan_region,
                                            ReserveForMutField));
            Ok(self.add_loan(loans, cmt, loan_region,
                             MutLoan(m_mutbl), pt, lp_elem))
        }
    }
}

fn mutate_borrowed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    cmt_base: mc::cmt,
    pointer_mutbl: ast::mutability,
    pointer_region: ty::Region) -> BckResult<LoansOrRoot>
{
    // See rule Mutate-Mut-Borrowck-Ptr in doc.rs

    if_ok!(self.check_mutable(cmt));
    self.mutate_or_freeze_mut_borrowed_ptr(
        cmt, loan_region, pt, cmt_base, pointer_mutbl, pointer_region,
        MutLoan(m_mutbl))
}

pub fn mutate_managed_ptr(
    self: &ComputeLoansContext,
    cmt: mc::cmt,
    loan_region: ty::Region,
    pt: PartialTotal,
    cmt_base: mc::cmt,
    derefs: uint,
    pointer_mutbl: ast::mutability) -> BckResult<LoansOrRoot>
{
    // See rule Mutate-Mut-Managed-Ptr in doc.rs

    self.mutate_or_freeze_mut_managed_ptr(
        cmt, loan_region, pt, cmt_base, derefs, pointer_mutbl)
}