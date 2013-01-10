// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use middle::pat_util;
use middle::ty;
use middle::ty::{CopyValue, MoveValue, ReadValue, ValueMode, ctxt};
use middle::typeck::{method_map, method_map_entry};

use core::vec;
use std::map::HashMap;
use syntax::ast::*;
use syntax::visit;
use syntax::visit::{fn_kind, vt};
use syntax::print::pprust;
use syntax::codemap::span;

struct VisitContext {
    tcx: ctxt,
    method_map: HashMap<node_id,method_map_entry>
}

enum UseMode {
    MoveMode,  // Move no matter what the type.
    ReadMode   // Read no matter what the type.
}

impl VisitContext {
    fn store_exprs(&self,
                   exprs; &[@expr],
                   visitor: vt<VisitContext>) {
        for exprs.each |expr| {
            self.store_expr(*expr, visitor);
        }
    }

    fn store_expr(&self,
                  expr: @expr,
                  visitor: vt<VisitContext>) {
        debug!("store_expr(expr=%?/%s)",
               expr.id,
               pprust::expr_to_str(expr, cx.tcx.sess.intr()));

        let mode = self.store_mode(expr.id);
        self.use_expr(expr, mode, visitor);
    }

    fn store_mode(&self, id: ast::node_id) -> UseMode {
        let node_ty = ty::node_id_to_type(self.tcx, id);
        debug!("store_mode(id=%d, node_ty=%s)",
               id,
               ppaux::ty_to_str(self.tcx, node_ty));
        if ty::type_implicitly_moves(self.tcx, node_ty) {
            MoveMode
        } else {
            ReadMode
        }
    }

    fn use_expr(&self,
                expr: @expr,
                mode: UseMode,
                visitor: vt<VisitContext>) {
        debug!("use_expr(expr=%?/%s, mode=%?)",
               expr.id, pprust::expr_to_str(expr, cx.tcx.sess.intr()),
               cx.mode);

        let mut mode = mode;

        // Adjust the mode if there was an implicit auto-ref or
        // auto-deref here.
        if self.tcx.adjustments.contains_key(expr.id) {
            mode = ReadValue;
        }

        match expr.node {
            expr_path(*) => {
                self.record_mode_for_expr(expr, mode);
            }

            expr_unary(deref, base) |     // *base
            expr_field(base, _, _) => {   // base.f
                // Moving out of *base or base.f moves out of base.
                self.use_expr(base, mode, visitor);
            }

            expr_index(lhs, rhs) => {          // lhs[rhs]
                // XXX overloaded operators
                self.use_expr(lhs, mode, visitor);
                self.store_expr(rhs, visitor);
            }

            expr_call(callee, args, _) => {    // callee(args)
                self.use_expr(callee, ReadValue, visitor);
                self.use_fn_args(callee.id, args, visitor);
            }

            expr_method_call(callee, _, _, args, _) => { // callee.m(args)
                let callee_mode = match cx.method_map.find(expr.id) {
                    Some(ref method_map_entry) => {
                        match method_map_entry.explicit_self {
                            sty_uniq(_) | sty_value => MoveValue,
                            _ => ReadValue
                        }
                    }
                    None => {
                        cx.tcx.sess.span_bug(expr.span, ~"no method map entry");
                    }
                };
                self.use_fn_arg(callee_mode, callee, visitor);
                self.use_fn_args(expr.callee_id, args, visitor);
            }

            expr_rec(ref fields, opt_with) |
            expr_struct(_, ref fields, opt_with) => {
                for fields.each |field| {
                    self.store_expr(field.expr, visitor);
                }

                for opt_with.each |with_expr| {
                    self.store_expr(with_expr, visitor);
                }
            }

            expr_tup(ref exprs) => {
                self.store_exprs(*exprs);
            }

            expr_if(cond_expr, ref then_blk, opt_else_expr) => {

                // XXX Interesting question:
                //   Is "copy if foo {expr1} else {expr2}" equivalent
                //   to "if foo {copy expr1} else {copy expr2}"?
                // I think not.

                self.store_expr(cond_expr, visitor);
                self.store_block(then_blk, visitor);
                for opt_else_expr.each |else_expr| {
                    self.store_expr(else_expr, visitor);
                }
            }

            expr_match(discr, arms) => {
                // We must do this first so that `arms_have_by_move_bindings`
                // below knows which bindings are moves.
                for arms.each |arm| {
                    self.use_arm(arm, mode, visitor);
                }

                let by_move_bindings_present =
                    pat_util::arms_have_by_move_bindings(cx.tcx, *arms);
                if by_move_bindings_present {
                    // If one of the arms moves a value out of the
                    // discriminant, then the discriminant itself is
                    // moved.
                    self.store_expr(discr, visitor);
                } else {
                    // Otherwise, the discriminant is merely read.
                    self.use_expr(discr, ReadValue, visitor);
                }
            }

            expr_copy(base) => {
                self.use_expr(base, ReadValue, visitor);
            }

            expr_paren(base) |
            expr_unary_move(base) => { // XXX this should be removed from AST
                self.use_expr(base, mode, visitor);
            }

            expr_vec(ref exprs, _) => {
                self.store_exprs(*exprs, visitor);
            }

            expr_addr_of(_, base) => {   // &base
                self.use_expr(base, ReadMode, visitor);
            }

            expr_break(*) |
            expr_again(*) |
            expr_lit(*) => {}

            expr_loop(blk, _) => {
                self.store_block(blk, visitor);
            }

            expr_log(_, a_expr, b_expr) => {
                self.store_expr(a_expr, visitor);
                self.store_expr(b_expr, visitor);
            }

            expr_assert(cond_expr) => {
                self.store_expr(cond_expr, visitor);
            }

            expr_while(cond_expr, blk) => {
                self.store_expr(cond_expr, visitor);
                self.store_block(blk, visitor);
            }

            expr_unary(_, lhs) => {
                // XXX overloaded operators
                self.store_expr(lhs, visitor);
            }

            expr_binary(_, lhs, rhs) => {
                // XXX overloaded operators
                self.store_expr(lhs, visitor);
                self.store_expr(rhs, visitor);
            }

            expr_block(ref blk) => {
                self.use_block(blk, mode, visitor);
            }

            expr_fail(ref opt_expr) |
            expr_ret(ref opt_expr) => {
                for opt_expr.each |expr| {
                    self.store_expr(expr, visitor);
                }
            }


            expr_fn(*) |
            expr_fn_block(*) |
            expr_loop_body(*) |
            expr_do_body(*) |
            expr_repeat(*) |
            expr_vstore(_, expr_vstore_slice) |
            expr_vstore(_, expr_vstore_mut_slice) |
            expr_vstore(_, expr_vstore_fixed(_)) |

            expr_cast(*) => {
                match smallintmap::find(*tcx.node_types, expr.id as uint) {
                    Some(t) => {
                        if ty::type_is_immediate(t) {
                            RvalueDatumExpr
                        } else {
                            RvalueDpsExpr
                        }
                    }
                    None => {
                        // Technically, it should not happen that the expr is not
                        // present within the table.  However, it DOES happen
                        // during type check, because the final types from the
                        // expressions are not yet recorded in the tcx.  At that
                        // time, though, we are only interested in knowing lvalue
                        // vs rvalue.  It would be better to base this decision on
                        // the AST type in cast node---but (at the time of this
                        // writing) it's not easy to distinguish casts to traits
                        // from other casts based on the AST.  This should be
                        // easier in the future, when casts to traits would like
                        // like @Foo, ~Foo, or &Foo.
                        RvalueDatumExpr
                    }
                }
            }

            expr_assign(*) |
            expr_swap(*) |
            expr_assign_op(*) => {
                RvalueStmtExpr
            }

            expr_vstore(_, expr_vstore_box) |
            expr_vstore(_, expr_vstore_mut_box) |
            expr_vstore(_, expr_vstore_uniq) => {
                RvalueDatumExpr
            }

            expr_mac(*) => {
                tcx.sess.span_bug(
                    expr.span,
                    ~"macro expression remains after expansion");
            }
        }
    }

    fn use_block(&self,
                 blk: &ast::blk,
                 mode: ValueMode,
                 visitor: vt<VisitContext>) {
        for blk.stmts.each |stmt| {
            visitor.visit_stmt(*stmt, *self, visitor);
        }
        self.use_expr(blk.expr, mode, visitor);
    }

    fn use_fn_args(&self,
                   callee_id: node_id,
                   arg_exprs: &[@expr],
                   visitor: vt<VisitContext>) {
        let arg_tys = ty::ty_fn_args(ty::node_id_to_type(cx.tcx, callee_id));
        for vec::each2(arg_exprs, arg_tys) |arg_expr, arg_ty| {
            let arg_mode = ty::resolved_mode(cx.tcx, arg_ty.mode);
            self.use_fn_args(arg_mode, arg_expr, visitor);
        }
    }

    fn use_fn_arg(&self,
                  arg_mode: rmode,
                  arg_expr: @expr,
                  visitor: vt<VisitContext>) {
        match arg_mode {
            by_ref => {
                self.use_expr(arg_expr, ReadValue, visitor);
            }
            by_val | by_move | by_copy => {
                self.use_expr(arg_expr, MoveValue, visitor);
            }
        }
    }
}

fn compute_modes_for_fn(fk: fn_kind,
                        decl: fn_decl,
                        body: blk,
                        sp: span,
                        id: node_id,
                        &&cx: VisitContext,
                        v: vt<VisitContext>) {
    let body_cx = VisitContext { mode: MoveValue, ..cx };
    visit::visit_fn(fk, decl, body, sp, id, body_cx, v);
}

fn compute_modes_for_fn_args(callee_id: node_id,
                             args: &[@expr],
                             last_arg_is_block: bool,
                             &&cx: VisitContext,
                             v: vt<VisitContext>) {
    let arg_tys = ty::ty_fn_args(ty::node_id_to_type(cx.tcx, callee_id));
    let mut i = 0;
    for vec::each2(args, arg_tys) |arg, arg_ty| {
        if last_arg_is_block && i == args.len() - 1 {
            let block_cx = VisitContext { mode: MoveValue, ..cx };
            compute_modes_for_expr(*arg, block_cx, v);
        } else {
            match ty::resolved_mode(cx.tcx, arg_ty.mode) {
                by_ref => {
                    let arg_cx = VisitContext { mode: ReadValue, ..cx };
                    compute_modes_for_expr(*arg, arg_cx, v);
                }
                by_val | by_move | by_copy => {
                    compute_modes_for_expr(*arg, cx, v);
                }
            }
        }
        i += 1;
    }
}

fn record_mode_for_expr(expr: @expr, &&cx: VisitContext) {
    match cx.mode {
        ReadValue | CopyValue => {
            cx.tcx.value_modes.insert(expr.id, cx.mode);
        }
        MoveValue => {
            // This is, contextually, a move, but if this expression
            // is implicitly copyable it's cheaper to copy.
            let e_ty = ty::expr_ty(cx.tcx, expr);
            if ty::type_implicitly_moves(cx.tcx, e_ty) {
                cx.tcx.value_modes.insert(expr.id, MoveValue);
            } else {
                cx.tcx.value_modes.insert(expr.id, CopyValue);
            }
        }
    }
}

fn compute_modes_for_expr(expr: @expr,
                          &&cx: VisitContext,
                          v: vt<VisitContext>) {
    debug!("compute_modes_for_expr(expr=%?/%s, mode=%?)",
           expr.id, pprust::expr_to_str(expr, cx.tcx.sess.intr()),
           cx.mode);

    // Adjust the mode if there was an implicit reference here.
    let cx = match cx.tcx.adjustments.find(expr.id) {
        None => cx,
        Some(adjustment) => {
            if adjustment.autoref.is_some() {
                VisitContext { mode: ReadValue, ..cx }
            } else {
                cx
            }
        }
    };

    match expr.node {
        expr_call(callee, args, is_block) => {
            let callee_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(callee, callee_cx, v);
            compute_modes_for_fn_args(callee.id, args, is_block, cx, v);
        }
        expr_path(*) => {
            record_mode_for_expr(expr, cx);
        }
        expr_copy(expr) => {
            let callee_cx = VisitContext { mode: CopyValue, ..cx };
            compute_modes_for_expr(expr, callee_cx, v);
        }
        expr_method_call(callee, _, _, args, is_block) => {
            // The LHS of the dot may or may not result in a move, depending
            // on the method map entry.
            let callee_mode;
            match cx.method_map.find(expr.id) {
                Some(ref method_map_entry) => {
                    match method_map_entry.explicit_self {
                        sty_uniq(_) | sty_value => callee_mode = MoveValue,
                        _ => callee_mode = ReadValue
                    }
                }
                None => {
                    cx.tcx.sess.span_bug(expr.span, ~"no method map entry");
                }
            }

            let callee_cx = VisitContext { mode: callee_mode, ..cx };
            compute_modes_for_expr(callee, callee_cx, v);

            compute_modes_for_fn_args(expr.callee_id, args, is_block, cx, v);
        }
        expr_binary(_, lhs, rhs) | expr_assign_op(_, lhs, rhs) => {
            // The signatures of these take their arguments by-ref, so they
            // don't copy or move.
            let arg_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(lhs, arg_cx, v);
            compute_modes_for_expr(rhs, arg_cx, v);
        }
        expr_addr_of(_, arg) => {
            // Takes its argument by-ref, so it doesn't copy or move.
            let arg_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(arg, arg_cx, v);
        }
        expr_unary(unop, arg) => {
            match unop {
                deref => {
                    // Derefs function as reads.
                    let arg_cx = VisitContext { mode: ReadValue, ..cx };
                    compute_modes_for_expr(arg, arg_cx, v);

                    // This is an lvalue, so it needs a value mode recorded
                    // for it.
                    record_mode_for_expr(expr, cx);
                }
                box(_) | uniq(_) => {
                    let arg_cx = VisitContext { mode: MoveValue, ..cx };
                    compute_modes_for_expr(arg, arg_cx, v);
                }
                not | neg => {
                    // Takes its argument by ref.
                    let arg_cx = VisitContext { mode: ReadValue, ..cx };
                    compute_modes_for_expr(arg, arg_cx, v);
                }
            }
        }
        expr_field(arg, _, _) => {
            let arg_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(arg, arg_cx, v);

            record_mode_for_expr(expr, cx);
        }
        expr_assign(lhs, rhs) => {
            // The signatures of these take their arguments by-ref, so they
            // don't copy or move.
            let arg_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(lhs, arg_cx, v);
            compute_modes_for_expr(rhs, cx, v);
        }
        expr_swap(lhs, rhs) => {
            let arg_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(lhs, arg_cx, v);
            compute_modes_for_expr(rhs, arg_cx, v);
        }
        expr_index(lhs, rhs) => {
            let lhs_cx = VisitContext { mode: ReadValue, ..cx };
            compute_modes_for_expr(lhs, lhs_cx, v);
            let rhs_cx = VisitContext { mode: MoveValue, ..cx };
            compute_modes_for_expr(rhs, rhs_cx, v);

            record_mode_for_expr(expr, cx);
        }
        expr_paren(arg) => {
            compute_modes_for_expr(arg, cx, v);
            record_mode_for_expr(expr, cx);
        }
        expr_match(head, ref arms) => {
            // We must do this first so that `arms_have_by_move_bindings`
            // below knows which bindings are moves.
            for arms.each |arm| {
                (v.visit_arm)(*arm, cx, v);
            }

            let by_move_bindings_present =
                pat_util::arms_have_by_move_bindings(cx.tcx, *arms);
            if by_move_bindings_present {
                // Propagate the current mode flag downward.
                visit::visit_expr(expr, cx, v);
            } else {
                // We aren't moving into any pattern, so this is just a read.
                let head_cx = VisitContext { mode: ReadValue, ..cx };
                compute_modes_for_expr(head, head_cx, v);
            }
        }
        _ => {
            // XXX: Spell out every expression above so when we add them we
            // don't forget to update this file.
            visit::visit_expr(expr, cx, v)
        }
    }
}

fn compute_modes_for_pat(pat: @pat,
                         &&cx: VisitContext,
                         v: vt<VisitContext>) {
    match pat.node {
        pat_ident(bind_infer, _, _)
                if pat_util::pat_is_binding(cx.tcx.def_map, pat) => {
            if ty::type_implicitly_moves(cx.tcx, ty::pat_ty(cx.tcx, pat)) {
                cx.tcx.value_modes.insert(pat.id, MoveValue);
            } else {
                cx.tcx.value_modes.insert(pat.id, CopyValue);
            }
        }
        _ => {}
    }

    visit::visit_pat(pat, cx, v);
}

pub fn compute_modes(tcx: ctxt, method_map: method_map, crate: @crate) {
    let visitor = visit::mk_vt(@visit::Visitor {
        visit_fn: compute_modes_for_fn,
        visit_expr: compute_modes_for_expr,
        visit_pat: compute_modes_for_pat,
        .. *visit::default_visitor()
    });
    let callee_cx = VisitContext {
        tcx: tcx,
        method_map: method_map,
        mode: MoveValue
    };
    visit::visit_crate(*crate, callee_cx, visitor);
}

