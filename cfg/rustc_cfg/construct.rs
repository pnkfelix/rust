// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::*;
use rustc::middle::graph;
use rustc::middle::typeck;
use rustc::middle::ty;
use std::vec::Vec;
use std::cell::RefCell;
use syntax::ast;
use syntax::ast_util;
use syntax::parse::token;
use rustc::util::nodemap::NodeMap;

struct CFGBuilder<'a> {
    tcx: &'a ty::ctxt,
    method_map: typeck::MethodMap,
    exit_map: NodeMap<CFGIndex>,
    graph: CFGGraph,
    loop_scopes: Vec<LoopScope> ,
    depth: &'a RefCell<int>,
}

struct Entered<'a> {
    context: &'a str,
    depth: &'a RefCell<int>
}

#[unsafe_destructor]
impl<'a> Drop for Entered<'a> {
    fn drop(&mut self) {
        *self.depth.borrow_mut() -= 1;
        let d = self.depth.get();
        assert!(d >= 0);
        debug!("{:s} exit {:s}", "  ".repeat(d as uint), self.context);
    }
}

impl<'a> CFGBuilder<'a> {
    fn enter(&self, context: &'a str) -> Entered<'a> {
        let d = self.depth.get();
        assert!(d >= 0);
        debug!("{:s} call {:s}", "  ".repeat(d as uint), context);
        *self.depth.borrow_mut() += 1;
        Entered{ context: context, depth: self.depth }
    }
}

struct LoopScope {
    loop_id: ast::NodeId,     // id of loop/while node
    continue_index: CFGIndex, // where to go on a `loop`
    break_index: CFGIndex,    // where to go on a `break
}

pub fn construct(tcx: &ty::ctxt,
                 method_map: typeck::MethodMap,
                 blk: &ast::Block) -> CFG {
    let depth = RefCell::new(0);
    let mut cfg_builder = CFGBuilder {
        exit_map: NodeMap::new(),
        graph: graph::Graph::new(),
        tcx: tcx,
        method_map: method_map,
        loop_scopes: Vec::new(),
        depth: &depth,
    };
    let entry = cfg_builder.add_node(0, []);
    let exit = cfg_builder.block(blk, entry);
    let CFGBuilder {exit_map, graph, ..} = cfg_builder;
    CFG {exit_map: exit_map,
         graph: graph,
         entry: entry,
         exit: exit}
}

impl<'a> CFGBuilder<'a> {
    fn block(&mut self, blk: &ast::Block, pred: CFGIndex) -> CFGIndex {
        let m = format!("CFGBuilder.block(blk, pred)");
        let _e = self.enter(m);
        let mut stmts_exit = pred;
        for &stmt in blk.stmts.iter() {
            stmts_exit = self.stmt(stmt, stmts_exit);
        }

        let expr_exit = self.opt_expr(blk.expr, stmts_exit);

        self.add_node(blk.id, [expr_exit])
    }

    fn stmt(&mut self, stmt: @ast::Stmt, pred: CFGIndex) -> CFGIndex {
        let m = format!("CFGBuilder.stmt(stmt, pred)");
        let _e = self.enter(m);
        match stmt.node {
            ast::StmtDecl(decl, _) => {
                self.decl(decl, pred)
            }

            ast::StmtExpr(expr, _) | ast::StmtSemi(expr, _) => {
                self.expr(expr, pred)
            }

            ast::StmtMac(..) => {
                self.tcx.sess.span_bug(stmt.span, "unexpanded macro");
            }
        }
    }

    fn decl(&mut self, decl: @ast::Decl, pred: CFGIndex) -> CFGIndex {
        let m = format!("CFGBuilder.decl(decl, pred)");
        let _e = self.enter(m);
        match decl.node {
            ast::DeclLocal(local) => {
                let init_exit = self.opt_expr(local.init, pred);
                self.pat(local.pat, init_exit)
            }

            ast::DeclItem(_) => {
                pred
            }
        }
    }

    fn pat(&mut self, pat: @ast::Pat, pred: CFGIndex) -> CFGIndex {
        let m = format!("CFGBuilder.pat(pat, pred");
        let _e = self.enter(m);
        match pat.node {
            ast::PatIdent(_, _, None) |
            ast::PatEnum(_, None) |
            ast::PatLit(..) |
            ast::PatRange(..) |
            ast::PatWild | ast::PatWildMulti => {
                self.add_node(pat.id, [pred])
            }

            ast::PatUniq(subpat) |
            ast::PatRegion(subpat) |
            ast::PatIdent(_, _, Some(subpat)) => {
                let subpat_exit = self.pat(subpat, pred);
                self.add_node(pat.id, [subpat_exit])
            }

            ast::PatEnum(_, Some(ref subpats)) |
            ast::PatTup(ref subpats) => {
                let pats_exit =
                    self.pats_all(subpats.iter().map(|p| *p), pred);
                self.add_node(pat.id, [pats_exit])
            }

            ast::PatStruct(_, ref subpats, _) => {
                let pats_exit =
                    self.pats_all(subpats.iter().map(|f| f.pat), pred);
                self.add_node(pat.id, [pats_exit])
            }

            ast::PatVec(ref pre, ref vec, ref post) => {
                let pre_exit =
                    self.pats_all(pre.iter().map(|p| *p), pred);
                let vec_exit =
                    self.pats_all(vec.iter().map(|p| *p), pre_exit);
                let post_exit =
                    self.pats_all(post.iter().map(|p| *p), vec_exit);
                self.add_node(pat.id, [post_exit])
            }
        }
    }

    fn pats_all<I: Iterator<@ast::Pat>>(&mut self,
                                        pats: I,
                                        pred: CFGIndex) -> CFGIndex {
        //! Handles case where all of the patterns must match.
        let m = format!("CFGBuilder.pats_all(pats, pred)");
        let _e = self.enter(m);

        let mut pats = pats;
        pats.fold(pred, |pred, pat| self.pat(pat, pred))
    }

    fn pats_any(&mut self,
                pats: &[@ast::Pat],
                pred: CFGIndex) -> CFGIndex {
        //! Handles case where just one of the patterns must match.
        let m = format!("CFGBuilder.pats_any(pats, pred)");
        let _e = self.enter(m);

        if pats.len() == 1 {
            self.pat(pats[0], pred)
        } else {
            let collect = self.add_dummy_node([]);
            for &pat in pats.iter() {
                let pat_exit = self.pat(pat, pred);
                self.add_contained_edge(pat_exit, collect);
            }
            collect
        }
    }

    fn expr(&mut self, expr: @ast::Expr, pred: CFGIndex) -> CFGIndex {
        let m = format!("CFGBuilder.expr(expr, pred) id: {}", expr.id);
        let _e = self.enter(m);

        match expr.node {
            ast::ExprBlock(blk) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprBlock id: {}", expr.id);
                let _e = self.enter(m);
                let blk_exit = self.block(blk, pred);
                self.add_node(expr.id, [blk_exit])
            }

            ast::ExprIf(cond, then, None) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprIf(_, _, None) id: {}", expr.id);
                let _e = self.enter(m);
                //
                //     [pred]
                //       |
                //       v 1
                //     [cond]
                //       |
                //      / \
                //     /   \
                //    v 2   *
                //  [then]  |
                //    |     |
                //    v 3   v 4
                //   [..expr..]
                //
                let cond_exit = self.expr(cond, pred);                // 1
                let then_exit = self.block(then, cond_exit);          // 2
                self.add_node(expr.id, [cond_exit, then_exit])        // 3,4
            }

            ast::ExprIf(cond, then, Some(otherwise)) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprIf(_, _, Some(_)) id: {}", expr.id);
                let _e = self.enter(m);
                //
                //     [pred]
                //       |
                //       v 1
                //     [cond]
                //       |
                //      / \
                //     /   \
                //    v 2   v 3
                //  [then][otherwise]
                //    |     |
                //    v 4   v 5
                //   [..expr..]
                //
                let cond_exit = self.expr(cond, pred);                // 1
                let then_exit = self.block(then, cond_exit);          // 2
                let else_exit = self.expr(otherwise, cond_exit);      // 3
                self.add_node(expr.id, [then_exit, else_exit])        // 4, 5
            }

            ast::ExprWhile(cond, body) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprWhile id: {}", expr.id);
                let _e = self.enter(m);
                //
                //         [pred]
                //           |
                //           v 1
                //       [loopback] <--+ 5
                //           |         |
                //           v 2       |
                //   +-----[cond]      |
                //   |       |         |
                //   |       v 4       |
                //   |     [body] -----+
                //   v 3
                // [expr]
                //
                // Note that `break` and `loop` statements
                // may cause additional edges.

                // Is the condition considered part of the loop?
                let loopback = self.add_dummy_node([pred]);           // 1
                let cond_exit = self.expr(cond, loopback);            // 2
                let expr_exit = self.add_node(expr.id, [cond_exit]);  // 3
                self.loop_scopes.push(LoopScope {
                    loop_id: expr.id,
                    continue_index: loopback,
                    break_index: expr_exit
                });
                let body_exit = self.block(body, cond_exit);          // 4
                self.add_contained_edge(body_exit, loopback);         // 5
                expr_exit
            }

            ast::ExprForLoop(..) => fail!("non-desugared expr_for_loop"),

            ast::ExprLoop(body, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprLoop id: {}", expr.id);
                let _e = self.enter(m);
                //
                //     [pred]
                //       |
                //       v 1
                //   [loopback] <---+
                //       |      4   |
                //       v 3        |
                //     [body] ------+
                //
                //     [expr] 2
                //
                // Note that `break` and `loop` statements
                // may cause additional edges.

                let loopback = self.add_dummy_node([pred]);           // 1
                let expr_exit = self.add_node(expr.id, []);           // 2
                self.loop_scopes.push(LoopScope {
                    loop_id: expr.id,
                    continue_index: loopback,
                    break_index: expr_exit,
                });
                let body_exit = self.block(body, loopback);           // 3
                self.add_contained_edge(body_exit, loopback);         // 4
                self.loop_scopes.pop();
                expr_exit
            }

            ast::ExprMatch(discr, ref arms) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprMatch id: {}", expr.id);
                let _e = self.enter(m);
                //
                //     [pred]
                //       |
                //       v 1
                //    [discr]
                //       |
                //       v 2
                //    [guard1]
                //      /  \
                //     |    \
                //     v 3  |
                //  [pat1]  |
                //     |
                //     v 4  |
                // [body1]  v
                //     |  [guard2]
                //     |    /   \
                //     | [body2] \
                //     |    |   ...
                //     |    |    |
                //     v 5  v    v
                //   [....expr....]
                //
                let discr_exit = self.expr(discr, pred);                 // 1

                let expr_exit = self.add_node(expr.id, []);
                let mut guard_exit = discr_exit;
                for arm in arms.iter() {
                    guard_exit = self.opt_expr(arm.guard, guard_exit); // 2
                    let pats_exit = self.pats_any(arm.pats.as_slice(),
                                                  guard_exit); // 3
                    let body_exit = self.expr(arm.body, pats_exit);      // 4
                    self.add_contained_edge(body_exit, expr_exit);       // 5
                }
                expr_exit
            }

            ast::ExprBinary(op, l, r) if ast_util::lazy_binop(op) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprBinary lazy_binop id: {}", expr.id);
                let _e = self.enter(m);
                //
                //     [pred]
                //       |
                //       v 1
                //      [l]
                //       |
                //      / \
                //     /   \
                //    v 2  *
                //   [r]   |
                //    |    |
                //    v 3  v 4
                //   [..exit..]
                //
                let l_exit = self.expr(l, pred);                         // 1
                let r_exit = self.expr(r, l_exit);                       // 2
                self.add_node(expr.id, [l_exit, r_exit])                 // 3,4
            }

            ast::ExprRet(v) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprRet id: {}", expr.id);
                let _e = self.enter(m);
                let v_exit = self.opt_expr(v, pred);
                let loop_scope = *self.loop_scopes.get(0);
                self.add_exiting_edge(expr, v_exit,
                                      loop_scope, loop_scope.break_index);
                self.add_node(expr.id, [])
            }

            ast::ExprBreak(label) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprBreak id: {}", expr.id);
                let _e = self.enter(m);
                let loop_scope = self.find_scope(expr, label);
                let b = self.add_node(expr.id, [pred]);
                self.add_exiting_edge(expr, b,
                                      loop_scope, loop_scope.break_index);
                self.add_node(ast::DUMMY_NODE_ID, [])
            }

            ast::ExprAgain(label) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprAgain id: {}", expr.id);
                let _e = self.enter(m);
                let loop_scope = self.find_scope(expr, label);
                let a = self.add_node(expr.id, [pred]);
                self.add_exiting_edge(expr, a,
                                      loop_scope, loop_scope.continue_index);
                self.add_node(ast::DUMMY_NODE_ID, [])
            }

            ast::ExprVec(ref elems, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprVec id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, elems.as_slice())
            }

            ast::ExprCall(func, ref args) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprCall id: {}", expr.id);
                let _e = self.enter(m);
                self.call(expr, pred, func, args.as_slice())
            }

            ast::ExprMethodCall(_, _, ref args) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprMethodCall id: {}", expr.id);
                let _e = self.enter(m);
                self.call(expr, pred, *args.get(0), args.slice_from(1))
            }

            ast::ExprIndex(l, r) if self.is_method_call(expr) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprIndex method_call id: {}", expr.id);
                let _e = self.enter(m);
                self.call(expr, pred, l, [r])
            }
            ast::ExprBinary(_, l, r) if self.is_method_call(expr) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprBinary method_call id: {}", expr.id);
                let _e = self.enter(m);
                self.call(expr, pred, l, [r])
            }

            ast::ExprUnary(_, e) if self.is_method_call(expr) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprUnary method_call id: {}", expr.id);
                let _e = self.enter(m);
                self.call(expr, pred, e, [])
            }

            ast::ExprTup(ref exprs) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprTup id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, exprs.as_slice())
            }

            ast::ExprStruct(_, ref fields, base) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprStruct id: {}", expr.id);
                let _e = self.enter(m);
                let base_exit = self.opt_expr(base, pred);
                let field_exprs: Vec<@ast::Expr> =
                    fields.iter().map(|f| f.expr).collect();
                self.straightline(expr, base_exit, field_exprs.as_slice())
            }

            ast::ExprRepeat(elem, count, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprRepeat id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [elem, count])
            }

            ast::ExprAssign(l, r) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprAssign id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [r, l])
            }
            ast::ExprAssignOp(_, l, r) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprAssignOp id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [r, l])
            }

            ast::ExprIndex(l, r) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprIndex id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [l, r])
            }
            ast::ExprBinary(_, l, r) => { // NB: && and || handled earlier
                let m = format!("CFGBuilder.expr(expr, pred) ExprBinary id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [l, r])
            }

            ast::ExprBox(p, e) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprBox id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [p, e])
            }

            ast::ExprAddrOf(_, e) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprAddrOf id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }
            ast::ExprCast(e, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprCast id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }
            ast::ExprUnary(_, e) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprUnary id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }
            ast::ExprParen(e) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprParen id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }
            ast::ExprVstore(e, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprVstore id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }

            ast::ExprField(e, _, _) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprField id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [e])
            }

            ast::ExprMac(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprMac id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
            ast::ExprInlineAsm(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprInlineAsm id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
            ast::ExprFnBlock(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprFnBlock id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
            ast::ExprProc(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprProc id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
            ast::ExprLit(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprLit id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
            ast::ExprPath(..) => {
                let m = format!("CFGBuilder.expr(expr, pred) ExprPath id: {}", expr.id);
                let _e = self.enter(m);
                self.straightline(expr, pred, [])
            }
        }
    }

    fn call(&mut self,
            call_expr: @ast::Expr,
            pred: CFGIndex,
            func_or_rcvr: @ast::Expr,
            args: &[@ast::Expr]) -> CFGIndex {
        let _e = self.enter("CFGBuilder.call(call_expr, pred, func_or_rcvr, args)");
        let func_or_rcvr_exit = self.expr(func_or_rcvr, pred);
        self.straightline(call_expr, func_or_rcvr_exit, args)
    }

    fn exprs(&mut self,
             exprs: &[@ast::Expr],
             pred: CFGIndex) -> CFGIndex {
        //! Constructs graph for `exprs` evaluated in order
        let _e = self.enter("CFGBuilder.exprs(exprs, pred)");

        exprs.iter().fold(pred, |p, &e| self.expr(e, p))
    }

    fn opt_expr(&mut self,
                opt_expr: Option<@ast::Expr>,
                pred: CFGIndex) -> CFGIndex {
        //! Constructs graph for `opt_expr` evaluated, if Some
        let _e = self.enter("CFGBuilder.opt_expr(opt_expr, pred)");

        opt_expr.iter().fold(pred, |p, &e| self.expr(e, p))
    }

    fn straightline(&mut self,
                    expr: @ast::Expr,
                    pred: CFGIndex,
                    subexprs: &[@ast::Expr]) -> CFGIndex {
        //! Handles case of an expression that evaluates `subexprs` in order
        let _e = self.enter("CFGBuilder.straightline(expr, pred, subexprs)");

        let subexprs_exit = self.exprs(subexprs, pred);
        self.add_node(expr.id, [subexprs_exit])
    }

    fn add_dummy_node(&mut self, preds: &[CFGIndex]) -> CFGIndex {
        let _e = self.enter("CFGBuilder.add_dummy_node(preds)");
        let ret = self.add_node(ast::DUMMY_NODE_ID, preds);
        ret
    }

    fn add_node(&mut self, id: ast::NodeId, preds: &[CFGIndex]) -> CFGIndex {
        let msg = format!("CFGBuilder.add_node(id, preds) id: {}", id);
        let _e = self.enter(msg);
        let node = self.graph.add_node(CFGNodeData {id: id});
        if id != ast::DUMMY_NODE_ID {
            assert!(!self.exit_map.contains_key(&id));
            self.exit_map.insert(id, node);
        }
        for &pred in preds.iter() {
            self.add_contained_edge(pred, node);
        }
        node
    }

    fn add_contained_edge(&mut self,
                          source: CFGIndex,
                          target: CFGIndex) {
        let _e = self.enter("CFGBuilder.add_contained_edge(source, target)");
        let data = CFGEdgeData {exiting_scopes: vec!()};
        self.graph.add_edge(source, target, data);
    }

    fn add_exiting_edge(&mut self,
                        from_expr: @ast::Expr,
                        from_index: CFGIndex,
                        to_loop: LoopScope,
                        to_index: CFGIndex) {
        let _e = self.enter("CFGBuilder.add_exiting_edge(from_expr, from_index, to_loop, to_index)");
        let mut data = CFGEdgeData {exiting_scopes: vec!()};
        let mut scope_id = from_expr.id;
        while scope_id != to_loop.loop_id {
            data.exiting_scopes.push(scope_id);
            scope_id = self.tcx.region_maps.encl_scope(scope_id);
        }
        self.graph.add_edge(from_index, to_index, data);
    }

    fn find_scope(&self,
                  expr: @ast::Expr,
                  label: Option<ast::Ident>) -> LoopScope {
        let _e = self.enter("CFGBuilder.find_scope(expr, label)");
        match label {
            None => {
                let _e = self.enter("CFGBuilder.find_scope(expr, label) None");
                return *self.loop_scopes.last().unwrap();
            }

            Some(the_label) => {
                let _e = self.enter("CFGBuilder.find_scope(expr, label) Some(_)");
                let def_map = self.tcx.def_map.borrow();
                match def_map.find(&expr.id) {
                    Some(&ast::DefLabel(loop_id)) => {
                        for l in self.loop_scopes.iter() {
                            if l.loop_id == loop_id {
                                return *l;
                            }
                        }
                        self.tcx.sess.span_bug(
                            expr.span,
                            format!("no loop scope for id {:?}", loop_id));
                    }

                    r => {
                        self.tcx.sess.span_bug(
                            expr.span,
                            format!("bad entry `{:?}` in def_map for expr.id (`{}`) [unused input label `{} ({:?})`]",
                                    r, expr.id, token::get_ident(the_label).get(), the_label));
                    }
                }
            }
        }
    }

    fn is_method_call(&self, expr: &ast::Expr) -> bool {
        let _e = self.enter("CFGBuilder.is_method_call(expr)");
        let method_call = typeck::MethodCall::expr(expr.id);
        self.method_map.borrow().contains_key(&method_call)
    }
}
