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
use mc = middle::mem_categorization;
use middle::pat_util;
use middle::ty::{ty_region};
use middle::ty;
use util::common::indenter;
use util::ppaux::{Repr};

use core::hashmap::HashSet;
use core::vec;
use syntax::ast::{m_const, m_imm, m_mutbl};
use syntax::ast;
use syntax::ast_util::id_range;
use syntax::codemap::span;
use syntax::print::pprust;
use syntax::visit;

mod lifetime;
mod restrictions;

/// Context used while gathering loans:
///
/// - `bccx`: the the borrow check context
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
    id_range: id_range,
    all_loans: @mut ~[Loan],
    item_ub: ast::node_id,
    repeating_ids: ~[ast::node_id],
    ignore_adjustments: HashSet<ast::node_id>
}

pub fn gather_loans(bccx: @BorrowckCtxt,
                    body: &ast::blk) -> (id_range, @mut ~[Loan]) {
    let glcx = @mut GatherLoanCtxt {
        bccx: bccx,
        id_range: id_range::max(),
        all_loans: @mut ~[],
        item_ub: body.node.id,
        repeating_ids: ~[body.node.id],
        ignore_adjustments: HashSet::new()
    };
    let v = visit::mk_vt(@visit::Visitor {visit_expr: gather_loans_in_expr,
                                          visit_block: gather_loans_in_block,
                                          visit_fn: gather_loans_in_fn,
                                          visit_stmt: add_stmt_to_map,
                                          visit_pat: add_pat_to_id_range,
                                          .. *visit::default_visitor()});
    (v.visit_block)(body, glcx, v);
    return (glcx.id_range, glcx.all_loans);
}

fn add_pat_to_id_range(p: @ast::pat,
                       self: @mut GatherLoanCtxt,
                       v: visit::vt<@mut GatherLoanCtxt>) {
    // NB: This visitor function just adds the pat ids into the id
    // range. We gather loans that occur in patterns using the
    // `gather_pat()` method below. Eventually these two should be
    // brought together.
    self.id_range.add(p.id);
    visit::visit_pat(p, self, v);
}

fn gather_loans_in_fn(fk: &visit::fn_kind,
                      decl: &ast::fn_decl,
                      body: &ast::blk,
                      sp: span,
                      id: ast::node_id,
                      self: @mut GatherLoanCtxt,
                      v: visit::vt<@mut GatherLoanCtxt>) {
    match fk {
        // Do not visit items here, the outer loop in borrowck/mod
        // will visit them for us in turn.
        &visit::fk_item_fn(*) | &visit::fk_method(*) |
        &visit::fk_dtor(*) => {
            return;
        }

        // Visit closures as part of the containing item.
        &visit::fk_anon(*) | &visit::fk_fn_block(*) => {
            self.push_repeating_id(body.node.id);
            visit::visit_fn(fk, decl, body, sp, id, self, v);
            self.pop_repeating_id(body.node.id);
        }
    }
}

fn gather_loans_in_block(blk: &ast::blk,
                         self: @mut GatherLoanCtxt,
                         vt: visit::vt<@mut GatherLoanCtxt>) {
    self.id_range.add(blk.node.id);
    visit::visit_block(blk, self, vt);
}

fn gather_loans_in_expr(ex: @ast::expr,
                        self: @mut GatherLoanCtxt,
                        vt: visit::vt<@mut GatherLoanCtxt>) {
    let bccx = self.bccx;
    let tcx = bccx.tcx;

    debug!("gather_loans_in_expr(expr=%?/%s)",
           ex.id, pprust::expr_to_str(ex, tcx.sess.intr()));

    self.id_range.add(ex.id);
    self.id_range.add(ex.callee_id);

    // If this expression is borrowed, have to ensure it remains valid:
    {
        let mut this = &mut *self; // FIXME(#5074)
        if !this.ignore_adjustments.contains(&ex.id) {
            for tcx.adjustments.find(&ex.id).each |&adjustments| {
                this.guarantee_adjustments(ex, *adjustments);
            }
        }
    }

    // Special checks for various kinds of expressions:
    match ex.node {
      ast::expr_addr_of(mutbl, base) => {
        let base_cmt = self.bccx.cat_expr(base);

        // make sure that the thing we are pointing out stays valid
        // for the lifetime `scope_r` of the resulting ptr:
        let scope_r = ty_region(tcx, ex.span, ty::expr_ty(tcx, ex));
        self.guarantee_valid(ex.id, ex.span, base_cmt, mutbl, scope_r);
        visit::visit_expr(ex, self, vt);
      }

      ast::expr_call(f, ref args, _) => {
        let arg_tys = ty::ty_fn_args(ty::expr_ty(self.tcx(), f));
        self.guarantee_arguments(ex, *args, arg_tys);
        visit::visit_expr(ex, self, vt);
      }

      ast::expr_method_call(_, _, _, ref args, _) => {
        let arg_tys = ty::ty_fn_args(ty::node_id_to_type(self.tcx(),
                                                         ex.callee_id));
        self.guarantee_arguments(ex, *args, arg_tys);

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
        assert!(id == popped);
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
                ast::by_copy => {}
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
               expr.repr(self.tcx()), adjustment);
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
                debug!("after autoderef, cmt=%s", cmt.repr(self.tcx()));

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
               cmt.repr(self.tcx()),
               req_mutbl,
               loan_region);
        let _i = indenter();

        let root_ub = { *self.repeating_ids.last() }; // FIXME(#5074)

        // Check that the lifetime of the borrow does not exceed
        // the lifetime of the data being borrowed.
        lifetime::guarantee_lifetime(self.bccx, self.item_ub, root_ub,
                                     borrow_span, cmt, loan_region, req_mutbl);

        // Check that we don't allow mutable borrows of non-mutable data.
        check_mutability(self.bccx, borrow_span, cmt, req_mutbl);

        // Compute the restrictions that are required to enforce the
        // loan is safe.
        let restr = restrictions::compute_restrictions(self.bccx, borrow_span,
                                                       cmt, req_mutbl);

        // Create the loan record (if needed).
        let loan = match restr {
            restrictions::Safe => {
                // No restrictions---no loan record necessary
                return;
            }

            restrictions::SafeIf(loan_path, restrictions) => {
                let loan_scope = match loan_region {
                    ty::re_scope(id) => id,
                    ty::re_free(ref fr) => fr.scope_id,

                    ty::re_static => {
                        // If we get here, an error must have been
                        // reported in
                        // `lifetime::guarantee_lifetime()`, because
                        // the only legal ways to have a borrow with a
                        // static lifetime should not require
                        // restrictions. To avoid reporting derived
                        // errors, we just return here without adding
                        // any loans.
                        return;
                    }

                    ty::re_bound(*) | ty::re_infer(*) => {
                        self.tcx().sess.span_bug(
                            cmt.span,
                            fmt!("Invalid borrow lifetime: %?", loan_region));
                    }
                };

                let kill_scope = self.compute_kill_scope(loan_scope, loan_path);

                let all_loans = &mut *self.all_loans; // FIXME(#5074)
                Loan {
                    index: all_loans.len(),
                    loan_path: loan_path,
                    cmt: cmt,
                    mutbl: req_mutbl,
                    gen_scope: borrow_id,
                    kill_scope: kill_scope,
                    span: borrow_span,
                    restrictions: restrictions
                }
            }
        };
        self.all_loans.push(loan);

        fn check_mutability(bccx: @BorrowckCtxt,
                            borrow_span: span,
                            cmt: mc::cmt,
                            req_mutbl: ast::mutability) {
            match req_mutbl {
                m_const | m_imm => {
                    // Data of any mutability can be lent as const or immutable.
                    // If the data is mutable, this is a freeze.
                }

                m_mutbl => {
                    // Only mutable data can be lent as mutable.
                    if !cmt.mutbl.is_mutable() {
                        bccx.report(BckError {span: borrow_span,
                                              cmt: cmt,
                                              code: err_mutbl(req_mutbl)});
                    }
                }
            }
        }
    }

    fn lexical_scope(&self, lp: @LoanPath) -> ast::node_id {
        match *lp {
            LpVar(local_id) => {
                let rm = self.bccx.tcx.region_maps;
                rm.encl_scope(local_id)
            }

            LpExtend(base, _, _) => self.lexical_scope(base)
        }
    }

    fn compute_kill_scope(&self,
                          loan_scope: ast::node_id,
                          lp: @LoanPath) -> ast::node_id {
        let lexical_scope = self.lexical_scope(lp);
        let rm = self.bccx.tcx.region_maps;
        if rm.is_subscope_of(lexical_scope, loan_scope) {
            lexical_scope
        } else {
            assert!(rm.is_subscope_of(loan_scope, lexical_scope));
            loan_scope
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
                        ty_region(self.tcx(), pat.span,
                                  ty::node_id_to_type(self.tcx(), pat.id));

                    // if the scope of the region ptr turns out to be
                    // specific to this arm, wrap the categorization
                    // with a cat_discr() node.  There is a detailed
                    // discussion of the function of this node in
                    // `lifetime.rs`:
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
                   self: @mut GatherLoanCtxt,
                   vt: visit::vt<@mut GatherLoanCtxt>) {
    match stmt.node {
        ast::stmt_expr(_, id) | ast::stmt_semi(_, id) => {
            self.bccx.stmt_map.insert(id);
        }
        _ => ()
    }
    visit::visit_stmt(stmt, self, vt);
}
