// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ----------------------------------------------------------------------
// Gathering loans
//
// The borrow check proceeds in two phases. In phase one, we gather the full
// set of loans that are required at any point.  These are sorted according to
// their associated scopes.  In phase two, checking loans, we will then make
// sure that all of these loans are honored.

use core::prelude::*;

use middle::borrowck::*;
use middle::borrowck::compute_loans::*;
use mc = middle::mem_categorization;
use middle::pat_util;
use middle::ty::{ty_region};
use middle::ty;
use util::common::indenter;
use util::ppaux::{expr_repr, region_to_str};

use core::hashmap::linear::LinearSet;
use core::vec;
use std::oldmap::HashMap;
use syntax::ast::{m_const, m_imm, m_mutbl};
use syntax::ast;
use syntax::codemap::span;
use syntax::print::pprust;
use syntax::visit;

/// Context used while gathering loans:
///
/// - `bccx`: the the borrow check context
/// - `req_maps`: the maps computed by `gather_loans()`, see def'n of the
///   struct `ReqMaps` for more info
/// - `item_ub`: the id of the block for the enclosing fn/method item
/// - `root_ub`: the id of the outermost block for which we can root
///   an `@T`.  This is the id of the innermost enclosing
///   loop or function body.
///
/// The role of `root_ub` is to prevent us from having to accumulate
/// vectors of rooted items at runtime.  Consider this case:
///
///     fn foo(...) -> int {
///         let mut ptr: &int;
///         while some_cond {
///             let x: @int = ...;
///             ptr = &*x;
///         }
///         *ptr
///     }
///
/// If we are not careful here, we would infer the scope of the borrow `&*x`
/// to be the body of the function `foo()` as a whole.  We would then
/// have root each `@int` that is produced, which is an unbounded number.
/// No good.  Instead what will happen is that `root_ub` will be set to the
/// body of the while loop and we will refuse to root the pointer `&*x`
/// because it would have to be rooted for a region greater than `root_ub`.
struct GatherLoanCtxt {
    bccx: @BorrowckCtxt,
    req_maps: ReqMaps,
    item_ub: ast::node_id,
    repeating_ids: ~[ast::node_id],
    ignore_adjustments: LinearSet<ast::node_id>
}

pub fn gather_loans(bccx: @BorrowckCtxt, crate: @ast::crate) -> ReqMaps {
    let glcx = @mut GatherLoanCtxt {
        bccx: bccx,
        req_maps: ReqMaps { req_loan_map: HashMap(), pure_map: HashMap() },
        item_ub: 0,
        repeating_ids: ~[],
        ignore_adjustments: LinearSet::new()
    };
    let v = visit::mk_vt(@visit::Visitor {visit_expr: req_loans_in_expr,
                                          visit_fn: req_loans_in_fn,
                                          visit_stmt: add_stmt_to_map,
                                          .. *visit::default_visitor()});
    visit::visit_crate(*crate, glcx, v);
    return glcx.req_maps;
}

fn req_loans_in_fn(fk: &visit::fn_kind,
                   decl: &ast::fn_decl,
                   body: &ast::blk,
                   sp: span,
                   id: ast::node_id,
                   &&self: @mut GatherLoanCtxt,
                   v: visit::vt<@mut GatherLoanCtxt>) {
    // see explanation attached to the `root_ub` field:
    let old_item_id = self.item_ub;
    match fk {
        &visit::fk_anon(*) | &visit::fk_fn_block(*) => {}
        &visit::fk_item_fn(*) | &visit::fk_method(*) |
        &visit::fk_dtor(*) => {
            self.item_ub = body.node.id;
        }
    }

    self.push_repeating_id(body.node.id);

    visit::visit_fn(fk, decl, body, sp, id, self, v);

    self.item_ub = old_item_id;
    self.pop_repeating_id(body.node.id);
}

fn req_loans_in_expr(ex: @ast::expr,
                     &&self: @mut GatherLoanCtxt,
                     vt: visit::vt<@mut GatherLoanCtxt>) {
    let bccx = self.bccx;
    let tcx = bccx.tcx;

    debug!("req_loans_in_expr(expr=%?/%s)",
           ex.id, pprust::expr_to_str(ex, tcx.sess.intr()));

    // If this expression is borrowed, have to ensure it remains valid:
    if !self.ignore_adjustments.contains(&ex.id) {
        for tcx.adjustments.find(&ex.id).each |adjustments| {
            self.guarantee_adjustments(ex, *adjustments);
        }
    }

    // Special checks for various kinds of expressions:
    match ex.node {
      ast::expr_addr_of(mutbl, base) => {
        let base_cmt = self.bccx.cat_expr(base);

        // make sure that the thing we are pointing out stays valid
        // for the lifetime `scope_r` of the resulting ptr:
        let scope_r = ty_region(ty::expr_ty(tcx, ex));
        self.guarantee_valid(ex.id, ex.span, base_cmt, mutbl, scope_r);
        visit::visit_expr(ex, self, vt);
      }

      ast::expr_call(f, ref args, _) => {
        let arg_tys = ty::ty_fn_args(ty::expr_ty(self.tcx(), f));
        self.guarantee_arguments(ex, *args, arg_tys);
        visit::visit_expr(ex, self, vt);
      }

      ast::expr_method_call(rcvr, _, _, ref args, _) => {
        let arg_tys = ty::ty_fn_args(ty::node_id_to_type(self.tcx(),
                                                         ex.callee_id));
        self.guarantee_arguments(ex, *args, arg_tys);

        match self.bccx.method_map.find(&ex.id) {
            Some(ref method_map_entry) => {
                match (*method_map_entry).explicit_self {
                    ast::sty_by_ref => {
                        self.guarantee_by_ref_argument(ex, rcvr);
                    }
                    _ => {} // Nothing to do.
                }
            }
            None => {
                self.tcx().sess.span_bug(ex.span, ~"no method map entry");
            }
        }

        visit::visit_expr(ex, self, vt);
      }

      ast::expr_match(ex_v, ref arms) => {
        let cmt = self.bccx.cat_expr(ex_v);
        for arms.each |arm| {
            for arm.pats.each |pat| {
                self.gather_pat(cmt, *pat, arm.body.node.id, ex.id);
            }
        }
        visit::visit_expr(ex, self, vt);
      }

      ast::expr_index(rcvr, _) |
      ast::expr_binary(_, rcvr, _) |
      ast::expr_unary(_, rcvr) |
      ast::expr_assign_op(_, rcvr, _)
      if self.bccx.method_map.contains_key(&ex.id) => {
        // Receivers in method calls are always passed by ref.
        //
        // Here, in an overloaded operator, the call is this expression,
        // and hence the scope of the borrow is this call.
        //
        // FIX? / NOT REALLY---technically we should check the other
        // argument and consider the argument mode.  But how annoying.
        // And this problem when goes away when argument modes are
        // phased out.  So I elect to leave this undone.
        let scope_r = ty::re_scope(ex.id);
        let rcvr_cmt = self.bccx.cat_expr(rcvr);
        self.guarantee_valid(rcvr.id, rcvr.span, rcvr_cmt, m_imm, scope_r);

        // FIXME (#3387): Total hack: Ignore adjustments for the left-hand
        // side. Their regions will be inferred to be too large.
        self.ignore_adjustments.insert(rcvr.id);

        visit::visit_expr(ex, self, vt);
      }

      // FIXME--#3387
      // ast::expr_binary(_, lhs, rhs) => {
      //     // Universal comparison operators like ==, >=, etc
      //     // take their arguments by reference.
      //     let lhs_ty = ty::expr_ty(self.tcx(), lhs);
      //     if !ty::type_is_scalar(lhs_ty) {
      //         let scope_r = ty::re_scope(ex.id);
      //         let lhs_cmt = self.bccx.cat_expr(lhs);
      //         self.guarantee_valid(lhs_cmt, m_imm, scope_r);
      //         let rhs_cmt = self.bccx.cat_expr(rhs);
      //         self.guarantee_valid(rhs_cmt, m_imm, scope_r);
      //     }
      //     visit::visit_expr(ex, self, vt);
      // }

      // see explanation attached to the `root_ub` field:
      ast::expr_while(cond, ref body) => {
          // during the condition, can only root for the condition
          self.push_repeating_id(cond.id);
          (vt.visit_expr)(cond, self, vt);
          self.pop_repeating_id(cond.id);

          // during body, can only root for the body
          self.push_repeating_id(body.node.id);
          (vt.visit_block)(body, self, vt);
          self.pop_repeating_id(body.node.id);
      }

      // see explanation attached to the `root_ub` field:
      ast::expr_loop(ref body, _) => {
          self.push_repeating_id(body.node.id);
          visit::visit_expr(ex, self, vt);
          self.pop_repeating_id(body.node.id);
      }

      _ => {
        visit::visit_expr(ex, self, vt);
      }
    }
}

pub impl GatherLoanCtxt {
    fn tcx(&self) -> ty::ctxt { self.bccx.tcx }

    fn push_repeating_id(&mut self, id: ast::node_id) {
        self.repeating_ids.push(id);
    }

    fn pop_repeating_id(&mut self, id: ast::node_id) {
        let popped = self.repeating_ids.pop();
        assert id == popped;
    }

    fn guarantee_arguments(&mut self,
                           call_expr: @ast::expr,
                           args: &[@ast::expr],
                           arg_tys: &[ty::arg]) {
        for vec::each2(args, arg_tys) |arg, arg_ty| {
            match ty::resolved_mode(self.tcx(), arg_ty.mode) {
                ast::by_ref => {
                    self.guarantee_by_ref_argument(call_expr, *arg);
                }
                ast::by_val | ast::by_copy => {}
            }
        }
    }

    fn guarantee_by_ref_argument(&mut self,
                                 call_expr: @ast::expr,
                                 arg_expr: @ast::expr) {
        let scope_r = ty::re_scope(call_expr.callee_id);
        let arg_cmt = self.bccx.cat_expr(arg_expr);
        self.guarantee_valid(arg_expr.id, arg_expr.span,
                             arg_cmt, m_imm, scope_r);
    }

    fn guarantee_adjustments(&mut self,
                             expr: @ast::expr,
                             adjustment: &ty::AutoAdjustment) {
        debug!("guarantee_adjustments(expr=%s, adjustment=%?)",
               expr_repr(self.tcx(), expr), adjustment);
        let _i = indenter();

        match *adjustment {
            ty::AutoAddEnv(*) => {
                debug!("autoaddenv -- no autoref");
                return;
            }

            ty::AutoDerefRef(
                ty::AutoDerefRef {
                    autoref: None, _ }) => {
                debug!("no autoref");
                return;
            }

            ty::AutoDerefRef(
                ty::AutoDerefRef {
                    autoref: Some(ref autoref),
                    autoderefs: autoderefs}) => {
                let mcx = &mc::mem_categorization_ctxt {
                    tcx: self.tcx(),
                    method_map: self.bccx.method_map};
                let mut cmt = mcx.cat_expr_autoderefd(expr, autoderefs);
                debug!("after autoderef, cmt=%s", self.bccx.cmt_to_repr(cmt));

                match autoref.kind {
                    ty::AutoPtr => {
                        self.guarantee_valid(expr.id,
                                             expr.span,
                                             cmt,
                                             autoref.mutbl,
                                             autoref.region)
                    }
                    ty::AutoBorrowVec | ty::AutoBorrowVecRef => {
                        let cmt_index = mcx.cat_index(expr, cmt);
                        self.guarantee_valid(expr.id,
                                             expr.span,
                                             cmt_index,
                                             autoref.mutbl,
                                             autoref.region)
                    }
                    ty::AutoBorrowFn => {
                        let cmt_deref = mcx.cat_deref_fn(expr, cmt, 0);
                        self.guarantee_valid(expr.id,
                                             expr.span,
                                             cmt_deref,
                                             autoref.mutbl,
                                             autoref.region)
                    }
                }
            }
        }
    }

    // Guarantees that addr_of(cmt) will be valid for the duration of
    // `static_scope_r`, or reports an error.  This may entail taking
    // out loans, which will be added to the `req_loan_map`.  This can
    // also entail "rooting" GC'd pointers, which means ensuring
    // dynamically that they are not freed.
    fn guarantee_valid(&mut self,
                       borrow_id: ast::node_id,
                       borrow_span: span,
                       cmt: mc::cmt,
                       req_mutbl: ast::mutability,
                       loan_region: ty::Region)
    {
        debug!("guarantee_valid(cmt=%s, req_mutbl=%?, loan_region=%?)",
               self.bccx.cmt_to_repr(cmt),
               req_mutbl,
               loan_region);
        let _i = indenter();

        let root_ub = { *self.repeating_ids.last() }; // FIXME(#5074)

        let clc = compute_loans::ComputeLoansContext {
            bccx: self.bccx,
            root_ub: root_ub,
            item_ub: self.item_ub,
            discr_scope: None,
            span: borrow_span
        };

        let result = match req_mutbl {
            m_mutbl => clc.mutate(cmt, loan_region, Total),
            m_imm => clc.freeze(cmt, loan_region, Total),
            m_const => clc.alias(cmt, loan_region, Total),
        };

        debug!("result=%?", result);

        match result {
            Ok(compute_loans::Loans(_, loans)) => {
                self.add_loans_to_expr(borrow_id, loans);
            }

            Ok(compute_loans::Root(key, root_info)) => {
                self.bccx.root_map.insert(key, root_info);
            }

            Ok(compute_loans::Purity(scope, err)) => {
                self.req_maps.pure_map.insert(scope, err);
            }

            Ok(compute_loans::Safe) => {
            }

            Err(e) => {
                self.bccx.report(e);
            }
        }
    }

    fn add_loans_to_expr(&mut self,
                         +borrow_id: ast::node_id,
                         +loans: ~[Loan]) {
        /*!
         *
         * Indicates the evaluation of `borrow_id` triggers
         * the loans `loans`.  They are therefore
         * added to the `req_loan_map` for use in
         * the `check_loans` phase.  Note: the loans will be
         * considered granted at the end of this expression,
         * and they stay in scope until the region `loan.scope`
         * is exited.
         */

        debug!("adding %u loans to scope %?: %s",
               loans.len(),
               borrow_id,
               str::connect(loans.map(|l| self.bccx.loan_to_repr(l)), ", "));

        match self.req_maps.req_loan_map.find(&borrow_id) {
            None => {
                self.req_maps.req_loan_map.insert(borrow_id, @mut loans);
            }
            Some(l) => {
                l.push_all(loans);
            }
        }
    }

    fn gather_pat(&mut self,
                  discr_cmt: mc::cmt,
                  root_pat: @ast::pat,
                  arm_body_id: ast::node_id,
                  match_id: ast::node_id) {
        do self.bccx.cat_pattern(discr_cmt, root_pat) |cmt, pat| {
            match pat.node {
              ast::pat_ident(bm, _, _) if self.pat_is_binding(pat) => {
                match bm {
                  ast::bind_by_ref(mutbl) => {
                    // ref x or ref x @ p --- creates a ptr which must
                    // remain valid for the scope of the match

                    // find the region of the resulting pointer (note that
                    // the type of such a pattern will *always* be a
                    // region pointer)
                    let scope_r =
                        ty_region(ty::node_id_to_type(self.tcx(), pat.id));

                    // if the scope of the region ptr turns out to be
                    // specific to this arm, wrap the categorization
                    // with a cat_discr() node.  There is a detailed
                    // discussion of the function of this node in
                    // compute_loans/mod.rs:
                    let arm_scope = ty::re_scope(arm_body_id);
                    if self.bccx.is_subregion_of(scope_r, arm_scope) {
                        let cmt_discr = self.bccx.cat_discr(cmt, match_id);
                        self.guarantee_valid(pat.id, pat.span,
                                             cmt_discr, mutbl, scope_r);
                    } else {
                        self.guarantee_valid(pat.id, pat.span,
                                             cmt, mutbl, scope_r);
                    }
                  }
                  ast::bind_by_copy | ast::bind_infer => {
                    // Nothing to do here; neither copies nor moves induce
                    // borrows.
                  }
                }
              }

              ast::pat_vec(_, Some(slice_pat), _) => {
                  // The `slice_pat` here creates a slice into the
                  // original vector.  This is effectively a borrow of
                  // the elements of the vector being matched.

                  let slice_ty = ty::node_id_to_type(self.tcx(),
                                                     slice_pat.id);
                  let (slice_mutbl, slice_r) =
                      self.vec_slice_info(slice_pat, slice_ty);
                  let mcx = self.bccx.mc_ctxt();
                  let cmt_index = mcx.cat_index(slice_pat, cmt);
                  self.guarantee_valid(pat.id, pat.span,
                                       cmt_index, slice_mutbl, slice_r);
              }

              _ => {}
            }
        }
    }

    fn vec_slice_info(&self,
                      pat: @ast::pat,
                      slice_ty: ty::t) -> (ast::mutability, ty::Region) {
        /*!
         *
         * In a pattern like [a, b, ..c], normally `c` has slice type,
         * but if you have [a, b, ..ref c], then the type of `ref c`
         * will be `&&[]`, so to extract the slice details we have
         * to recurse through rptrs.
         */

        match ty::get(slice_ty).sty {
            ty::ty_evec(slice_mt, ty::vstore_slice(slice_r)) => {
                (slice_mt.mutbl, slice_r)
            }

            ty::ty_rptr(_, ref mt) => {
                self.vec_slice_info(pat, mt.ty)
            }

            _ => {
                self.tcx().sess.span_bug(
                    pat.span,
                    fmt!("Type of slice pattern is not a slice"));
            }
        }
    }

    fn pat_is_variant_or_struct(&self, pat: @ast::pat) -> bool {
        pat_util::pat_is_variant_or_struct(self.bccx.tcx.def_map, pat)
    }

    fn pat_is_binding(&self, pat: @ast::pat) -> bool {
        pat_util::pat_is_binding(self.bccx.tcx.def_map, pat)
    }
}

// Setting up info that preserve needs.
// This is just the most convenient place to do it.
fn add_stmt_to_map(stmt: @ast::stmt,
                   &&self: @mut GatherLoanCtxt,
                   vt: visit::vt<@mut GatherLoanCtxt>) {
    match stmt.node {
        ast::stmt_expr(_, id) | ast::stmt_semi(_, id) => {
            self.bccx.stmt_map.insert(id, ());
        }
        _ => ()
    }
    visit::visit_stmt(stmt, self, vt);
}

