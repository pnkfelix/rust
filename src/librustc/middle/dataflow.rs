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
 * A module for propagating forward dataflow information. The analysis
 * assumes that the items to be propagated can be represented as bits
 * and thus uses bitvectors. Your job is simply to specify the so-called
 * GEN and KILL bits for each expression.
 */

use core::prelude::*;
use core::cast;
use core::uint;
use syntax::ast;
use syntax::ast_util;
use syntax::ast_util::id_range;
use middle::ty;
use middle::typeck;

trait DataFlowOperator {
    fn initial_value(&self) -> bool;
    fn join(&self, succ: uint, pred: uint) -> uint;
}

pub struct DataFlowContext<O> {
    priv tcx: ty::ctxt,
    priv method_map: typeck::method_map,
    priv oper: O,
    priv id_range: id_range,
    priv words_per_id: uint,
    priv gens: ~[uint],
    priv kills: ~[uint],
    priv on_entry: ~[uint]
}

struct PropagationContext<'self, O> {
    dfcx: &'self mut DataFlowContext<O>,
    changed: bool
}

struct LoopScope<'self> {
    continue_id: ast::node_id,
    break_bits: ~[uint]
}

impl<O:DataFlowOperator> DataFlowContext<O> {
    pub fn new(+tcx: ty::ctxt,
               +method_map: typeck::method_map,
               +oper: O) -> DataFlowContext<O> {
        DataFlowContext {
            tcx: tcx,
            method_map: method_map,
            words_per_id: 0,
            oper: oper,
            id_range: id_range {min: 0, max: 0},
            gens: ~[],
            kills: ~[],
            on_entry: ~[]
        }
    }

    pub fn init(&mut self,
                id_range: id_range,
                max_bits: uint) {
        self.id_range = id_range;

        self.words_per_id = (max_bits + uint::bits - 1) / uint::bits;

        let len = (id_range.max - id_range.min) as uint * self.words_per_id;
        self.gens = vec::from_elem(len, 0);
        self.kills = vec::from_elem(len, 0);
        let elem = if self.oper.initial_value() {uint::max_value} else {0};
        self.on_entry = vec::from_elem(len, elem);
    }

    pub fn add_gen(&mut self, id: ast::node_id, bit: uint) {
        //! Indicates that `id` generates `bit`

        set_bit(self.gens, self.words_per_id, id, bit);
    }

    pub fn add_kill(&mut self, id: ast::node_id, bit: uint) {
        //! Indicates that `id` kills `bit`

        set_bit(self.kills, self.words_per_id, id, bit);
    }

    fn apply_gen_kill(&self, id: ast::node_id, bits: &mut [uint]) {
        //! Applies the gen and kill sets for `id` to `bits`

        let (start, end) = compute_id_range(self.words_per_id, id);
        let gens = self.gens.slice(start, end);
        bitwise(bits, gens, |a, b| a | b);
        let kills = self.kills.slice(start, end);
        bitwise(bits, kills, |a, b| a & !b);
    }

    fn propagate(&mut self, blk: &ast::blk) {
        let mut propcx = PropagationContext {
            dfcx: self,
            changed: true
        };

        let mut temp = vec::from_elem(self.words_per_id, 0);
        let mut loop_scopes = ~[];

        while propcx.changed {
            propcx.changed = false;
            propcx.reset(temp);
            propcx.walk_block(blk, temp, &mut loop_scopes);
        }
    }
}

impl<'self, O:DataFlowOperator> PropagationContext<'self, O> {
    fn tcx(&self) -> ty::ctxt {
        self.dfcx.tcx
    }

    fn walk_block(&mut self,
                  blk: &ast::blk,
                  in_out: &mut [uint],
                  loop_scopes: &mut ~[LoopScope]) {
        self.merge_with_entry_set(blk.node.id, in_out);

        for blk.node.stmts.each |&stmt| {
            self.walk_stmt(stmt, in_out, loop_scopes);
        }

        self.walk_opt_expr(blk.node.expr, in_out, loop_scopes);

        self.dfcx.apply_gen_kill(blk.node.id, in_out);
    }

    fn walk_stmt(&mut self,
                 stmt: @ast::stmt,
                 in_out: &mut [uint],
                 loop_scopes: &mut ~[LoopScope]) {
        match stmt.node {
            ast::stmt_decl(decl, _) => {
                self.walk_decl(decl, in_out, loop_scopes);
            }

            ast::stmt_expr(expr, _) | ast::stmt_semi(expr, _) => {
                self.walk_expr(expr, in_out, loop_scopes);
            }

            ast::stmt_mac(*) => {
                self.tcx().sess.span_bug(stmt.span, ~"unexpanded macro");
            }
        }
    }

    fn walk_decl(&mut self,
                 decl: @ast::decl,
                 in_out: &mut [uint],
                 loop_scopes: &mut ~[LoopScope]) {
        match decl.node {
            ast::decl_local(ref locals) => {
                for locals.each |local| {
                    self.walk_opt_expr(local.node.init, in_out, loop_scopes);
                }
            }

            ast::decl_item(_) => {}
        }
    }

    fn walk_expr(&mut self,
                 expr: @ast::expr,
                 in_out: &mut [uint],
                 loop_scopes: &mut ~[LoopScope]) {
        self.merge_with_entry_set(expr.id, in_out);

        match expr.node {
            ast::expr_fn_block(_, ref blk) => {
                // we don't examine the contents of nested fns
            }

            ast::expr_if(cond, ref then, els) => {
                //
                //     (cond)
                //       |
                //       v
                //      ( )
                //     /   \
                //    |     |
                //    v     v
                //  (then)(els)
                //    |     |
                //    v     v
                //   (  succ  )
                //
                self.walk_expr(cond, in_out, loop_scopes);

                let mut then_bits = copy_vec(in_out);
                self.walk_block(then, then_bits, loop_scopes);

                self.walk_opt_expr(els, in_out, loop_scopes);
                add_bits(&self.dfcx.oper, then_bits, in_out);
            }

            ast::expr_while(cond, ref blk) => {
                //
                //     (expr) <--+
                //       |       |
                //       v       |
                //  +--(cond)    |
                //  |    |       |
                //  |    v       |
                //  v  (blk) ----+
                //       |
                //    <--+ (break)
                //

                self.walk_expr(cond, in_out, loop_scopes);

                let mut body_bits = copy_vec(in_out);
                loop_scopes.push(LoopScope {
                    continue_id: expr.id,
                    break_bits: copy_vec(in_out)
                });
                self.walk_block(blk, body_bits, loop_scopes);
                self.add_to_entry_set(expr.id, body_bits);
                let new_loop_scope = loop_scopes.pop();
                copy_bits(new_loop_scope.break_bits, in_out);
            }

            ast::expr_loop(ref blk, _) => {
                //
                //     (expr) <--+
                //       |       |
                //       v       |
                //     (blk) ----+
                //       |
                //    <--+ (break)
                //

                let mut body_bits = copy_vec(in_out);
                self.reset(in_out);
                loop_scopes.push(LoopScope {
                    continue_id: expr.id,
                    break_bits: copy_vec(in_out)
                });
                self.walk_block(blk, body_bits, loop_scopes);
                self.add_to_entry_set(expr.id, body_bits);

                let new_loop_scope = loop_scopes.pop();
                // FIXME() --- we can eliminate this copy after snapshot
                copy_bits(new_loop_scope.break_bits, in_out);
            }

            ast::expr_match(discr, ref arms) => {
                //
                //    (discr)
                //     / | \
                //    |  |  |
                //    v  v  v
                //   (..arms..)
                //    |  |  |
                //    v  v  v
                //   (  succ  )
                //
                //
                self.walk_expr(discr, in_out, loop_scopes);

                let mut guards = copy_vec(in_out);
                let mut temp = vec::from_elem(self.dfcx.words_per_id, 0);

                // We know that exactly one arm will be taken, so we
                // can start out with a blank slate and just union
                // together the bits from each arm:
                self.reset(in_out);

                for arms.each |arm| {
                    // in_out reflects the discr and all guards to date
                    self.walk_opt_expr(arm.guard, guards, loop_scopes);

                    // determine the bits for the body and then union
                    // them into `in_out`, which reflects all bodies to date
                    copy_bits(guards, temp);
                    self.walk_block(&arm.body, temp, loop_scopes);
                    add_bits(&self.dfcx.oper, temp, in_out);
                }
            }

            ast::expr_ret(o_e) => {
                self.walk_opt_expr(o_e, in_out, loop_scopes);
                self.reset(in_out);
            }

            ast::expr_break(opt_label) => {
                fail!(~"break");
            }

            ast::expr_again(opt_label) => {
                fail!(~"again");
            }

            ast::expr_assign(l, r) |
            ast::expr_assign_op(_, l, r) => {
                self.walk_expr(r, in_out, loop_scopes);
                self.walk_expr(l, in_out, loop_scopes);
            }

            ast::expr_swap(l, r) => {
                self.walk_expr(l, in_out, loop_scopes);
                self.walk_expr(r, in_out, loop_scopes);
            }

            ast::expr_vec(ref exprs, _) => {
                self.walk_exprs(*exprs, in_out, loop_scopes)
            }

            ast::expr_repeat(l, r, _) => {
                self.walk_expr(l, in_out, loop_scopes);
                self.walk_expr(r, in_out, loop_scopes);
            }

            ast::expr_struct(_, ref fields, with_expr) => {
                self.walk_opt_expr(with_expr, in_out, loop_scopes);
                for fields.each |field| {
                    self.walk_expr(field.node.expr, in_out, loop_scopes);
                }
            }

            ast::expr_call(f, ref args, _) => {
                self.walk_call(expr.callee_id, expr.id,
                               f, *args, in_out, loop_scopes);
            }

            ast::expr_method_call(rcvr, _, _, ref args, _) => {
                self.walk_call(expr.callee_id, expr.id,
                               rcvr, *args, in_out, loop_scopes);
            }

            ast::expr_index(l, r) |
            ast::expr_binary(_, l, r) if self.is_method_call(expr) => {
                self.walk_call(expr.callee_id, expr.id,
                               l, [r], in_out, loop_scopes);
            }

            ast::expr_unary(_, e) if self.is_method_call(expr) => {
                self.walk_call(expr.callee_id, expr.id,
                               e, [], in_out, loop_scopes);
            }

            ast::expr_tup(ref exprs) => {
                self.walk_exprs(*exprs, in_out, loop_scopes);
            }

            ast::expr_binary(op, l, r) if ast_util::lazy_binop(op) => {
                self.walk_expr(l, in_out, loop_scopes);
                let temp = copy_vec(in_out);
                self.walk_expr(r, in_out, loop_scopes);
                add_bits(&self.dfcx.oper, temp, in_out);
            }

            ast::expr_log(l, r) |
            ast::expr_index(l, r) |
            ast::expr_binary(_, l, r) => {
                self.walk_exprs([l, r], in_out, loop_scopes);
            }

            ast::expr_lit(*) |
            ast::expr_path(*) => {
            }

            ast::expr_addr_of(_, e) |
            ast::expr_copy(e) |
            ast::expr_loop_body(e) |
            ast::expr_do_body(e) |
            ast::expr_cast(e, _) |
            ast::expr_unary(_, e) |
            ast::expr_paren(e) |
            ast::expr_vstore(e, _) |
            ast::expr_field(e, _, _) => {
                self.walk_expr(e, in_out, loop_scopes);
            }

            ast::expr_inline_asm(ref inline_asm) => {
                for inline_asm.inputs.each |&(_, expr)| {
                    self.walk_expr(expr, in_out, loop_scopes);
                }
                for inline_asm.outputs.each |&(_, expr)| {
                    self.walk_expr(expr, in_out, loop_scopes);
                }
            }

            ast::expr_block(ref blk) => {
                self.walk_block(blk, in_out, loop_scopes);
            }

            ast::expr_mac(*) => {
                self.tcx().sess.span_bug(expr.span, ~"unexpanded macro");
            }
        }

        self.dfcx.apply_gen_kill(expr.id, in_out);
    }

    fn walk_exprs(&mut self,
                  exprs: &[@ast::expr],
                  in_out: &mut [uint],
                  loop_scopes: &mut ~[LoopScope]) {
        for exprs.each |&expr| {
            self.walk_expr(expr, in_out, loop_scopes);
        }
    }

    fn walk_opt_expr(&mut self,
                     opt_expr: Option<@ast::expr>,
                     in_out: &mut [uint],
                     loop_scopes: &mut ~[LoopScope]) {
        for opt_expr.each |&expr| {
            self.walk_expr(expr, in_out, loop_scopes);
        }
    }

    fn walk_call(&mut self,
                 callee_id: ast::node_id,
                 call_id: ast::node_id,
                 arg0: @ast::expr,
                 args: &[@ast::expr],
                 in_out: &mut [uint],
                 loop_scopes: &mut ~[LoopScope]) {
        self.walk_expr(arg0, in_out, loop_scopes);
        self.walk_exprs(args, in_out, loop_scopes);

        self.merge_with_entry_set(callee_id, in_out);
        self.dfcx.apply_gen_kill(callee_id, in_out);

        let return_ty = ty::node_id_to_type(self.tcx(), call_id);
        let fails = ty::type_is_bot(return_ty);
        if fails {
            self.reset(in_out);
        }
    }

    fn is_method_call(&self, expr: @ast::expr) -> bool {
        self.dfcx.method_map.contains_key(&expr.id)
    }

    fn reset(&mut self, bits: &mut [uint]) {
        let e = if self.dfcx.oper.initial_value() {uint::max_value} else {0};
        for vec::each_mut(bits) |b| { *b = e; }
    }

    fn add_to_entry_set(&mut self, id: ast::node_id, pred_bits: &[uint]) {
        let (start, end) = compute_id_range(self.dfcx.words_per_id, id);
        let changed = { // FIXME(#5074) awkward construction
            let on_entry = vec::mut_slice(self.dfcx.on_entry, start, end);
            add_bits(&self.dfcx.oper, pred_bits, on_entry)
        };
        if changed {
            self.changed = true;
        }
    }

    fn merge_with_entry_set(&mut self, id: ast::node_id, pred_bits: &mut [uint]) {
        let (start, end) = compute_id_range(self.dfcx.words_per_id, id);
        let changed = { // FIXME(#5074) awkward construction
            let on_entry = vec::mut_slice(self.dfcx.on_entry, start, end);
            let changed = add_bits(&self.dfcx.oper, reslice(pred_bits), on_entry);
            copy_bits(reslice(on_entry), pred_bits);
            changed
        };
        if changed {
            self.changed = true;
        }
    }
}

fn compute_id_range(words_per_id: uint,
                    id: ast::node_id) -> (uint, uint) {
    let start = (id as uint) * words_per_id;
    let end = start + words_per_id;
    (start, end)
}

fn copy_bits(in_vec: &[uint], out_vec: &mut [uint]) -> bool {
    bitwise(out_vec, in_vec, |_, b| b)
}

fn add_bits<O:DataFlowOperator>(oper: &O,
                                in_vec: &[uint],
                                out_vec: &mut [uint]) -> bool {
    bitwise(out_vec, in_vec, |a, b| oper.join(a, b))
}

#[inline(always)]
fn bitwise(out_vec: &mut [uint],
           in_vec: &[uint],
           op: &fn(uint, uint) -> uint) -> bool {
    assert_eq!(out_vec.len(), in_vec.len());
    let mut changed = false;
    for uint::range(0, out_vec.len()) |i| {
        let old_val = out_vec[i];
        let new_val = op(old_val, in_vec[i]);
        out_vec[i] = new_val;
        changed |= (old_val != new_val);
    }
    return changed;
}

fn transform_bit(bitvector: &mut [uint],
                 words_per_id: uint,
                 id: ast::node_id,
                 bit: uint,
                 f: &fn(uint, uint) -> uint) -> bool {
    let (start, end) = compute_id_range(words_per_id, id);
    let id_words = vec::mut_slice(bitvector, start, end);
    let word = bit / uint::bits;
    let bit_in_word = bit % uint::bits;
    let bit_mask = 1 << bit_in_word;
    let oldv = id_words[word];
    let newv = f(oldv, bit_mask);
    id_words[word] = newv;
    oldv != newv
}

fn set_bit(bitvector: &mut [uint],
           words_per_id: uint,
           id: ast::node_id,
           bit: uint) -> bool {
    transform_bit(bitvector, words_per_id, id, bit, |a, b| a | b)
}

fn copy_vec(v: &mut [uint]) -> ~[uint] {
    // FIXME(#5074) workaround borrow checker
    let mut r = ~[];
    for uint::range(0, v.len()) |i| {
        r.push(v[i]);
    }
    return r;
}

fn reslice<'a>(+v: &'a mut [uint]) -> &'a [uint] {
    // FIXME(#5074) workaround borrow checker
    unsafe {
        cast::transmute(v)
    }
}
