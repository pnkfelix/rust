/*

A classic liveness analysis based on dataflow over the AST.  Computes,
for each local variable in a function, whether that variable is live
at a given point.  Program execution points are identified by their
id.

# Basic idea

The basic model is that each local variable is assigned an index.  We
represent sets of local variables using a vector indexed by this
index.  The value in the vector is either 0, indicating the variable
is dead, or the id of an expression that uses the variable.

We conceptually walk over the AST in reverse execution order.  If we
find a use of a variable, we add it to the set of live variables.  If
we find an assignment to a variable, we remove it from the set of live
variables.  When we have to merge two flows, we take the union of
those two flows---if the variable is live on both paths, we simply
pick one id.  In the event of loops, we continue doing this until a
fixed point is reached.

## Checking initialization

At the function entry point, all variables must be dead.  If this is
not the case, we can report an error using the id found in the set of
live variables, which identifies a use of the variable which is not
dominated by an assignment.

## Checking moves

After each explicit move, the variable must be dead.

## Computing last uses

Any use of the variable where the variable is dead afterwards is a
last use.

# Extension to handle constructors

Each field is assigned an index just as with local variables.  A use of
`self` is considered a use of all fields.  A use of `self.f` is just a use
of `f`.

*/

import dvec::{dvec, extensions};
import std::map::{hashmap, int_hash};
import syntax::{visit, ast_util};
import syntax::print::pprust::{expr_to_str};
import visit::vt;
import syntax::codemap::span;
import syntax::ast::*;
import driver::session::session;
import io::writer_util;
import capture::{cap_move, cap_drop, cap_copy, cap_ref};

export check_crate;
export last_use_map;

type last_use_map = hashmap<node_id, @dvec<node_id>>;

enum variable = uint;
enum live_node = uint;

enum live_node_kind {
    lnk_freevar(span),
    lnk_expr(span),
    lnk_vdef(span),
    lnk_exit
}

fn check_crate(tcx: ty::ctxt,
               method_map: typeck::method_map,
               crate: @crate) -> last_use_map {
    let visitor = visit::mk_vt(@{
        visit_fn: visit_fn,
        visit_local: visit_local,
        visit_expr: visit_expr
        with *visit::default_visitor()
    });

    let last_use_map = int_hash();
    let initial_maps = @ir_maps(tcx, method_map, last_use_map);
    visit::visit_crate(*crate, initial_maps, visitor);
    tcx.sess.abort_if_errors();
    ret last_use_map;
}

impl of to_str::to_str for live_node {
    fn to_str() -> str { #fmt["ln(%u)", *self] }
}

impl of to_str::to_str for variable {
    fn to_str() -> str { #fmt["v(%u)", *self] }
}

// ______________________________________________________________________
// Creating ir_maps
//
// This is the first pass and the one that drives the main
// computation.  It walks up and down the IR once.  On the way down,
// we count for each function the number of variables as well as
// liveness nodes.  A liveness node is basically an expression or
// capture clause that does something of interest: either it has
// interesting control flow or it uses/defines a local variable.
//
// On the way back up, at each function node we create liveness sets
// (we now know precisely how big to make our various vectors and so
// forth) and then do the data-flow propagation to compute the set
// of live variables at each program point.
//
// Finally, we run back over the IR one last time and, using the
// computed liveness, check various safety conditions.  For example,
// there must be no live nodes at the definition site for a variable
// unless it has an initializer.  Similarly, each non-mutable local
// variable must not be assigned if there is some successor
// assignment.  And so forth.

impl methods for live_node {
    fn is_valid() -> bool { *self != uint::max_value }
}

fn invalid_node() -> live_node { live_node(uint::max_value) }

type capture_info = {ln: live_node, is_move: bool, var: variable};

fn tracked_var_id_from_def(def: def) -> option<node_id> {
    alt def {
      def_arg(nid, _) | def_local(nid, _) {some(nid)}
      _ {none}
    }
}

class ir_maps {
    let tcx: ty::ctxt;
    let method_map: typeck::method_map;
    let last_use_map: last_use_map;

    let mut num_live_nodes: uint;
    let mut num_vars: uint;
    let live_node_map: hashmap<node_id, live_node>;
    let variable_map: hashmap<node_id, variable>;
    let capture_map: hashmap<node_id, @[capture_info]>;
    let mut var_ids: [node_id];
    let mut lnks: [live_node_kind];
    let mut ret_ln: live_node;

    new(tcx: ty::ctxt, method_map: typeck::method_map,
        last_use_map: hashmap<node_id, @dvec<node_id>>) {
        self.tcx = tcx;
        self.method_map = method_map;
        self.last_use_map = last_use_map;

        self.num_live_nodes = 0u;
        self.num_vars = 0u;
        self.live_node_map = int_hash();
        self.variable_map = int_hash();
        self.capture_map = int_hash();
        self.var_ids = [];
        self.lnks = [];

        // node to represent the successor of ret or fail, where
        // nothing is ever live:
        self.ret_ln = invalid_node();
        self.ret_ln = self.add_live_node(lnk_exit);
    }

    fn add_live_node(lnk: live_node_kind) -> live_node {
        let ln = live_node(self.num_live_nodes);
        self.lnks += [lnk];
        self.num_live_nodes += 1u;

        #debug["%s is of kind %?", ln.to_str(), lnk];

        ln
    }

    fn add_live_node_for_node(node_id: node_id, lnk: live_node_kind) {
        let ln = self.add_live_node(lnk);
        self.live_node_map.insert(node_id, ln);

        #debug["%s is node %d", ln.to_str(), node_id];
    }

    fn add_variable(node_id: node_id) {
        let v = variable(self.num_vars);
        self.variable_map.insert(node_id, v);
        self.var_ids += [node_id];
        self.num_vars += 1u;

        #debug["%s is node %d", v.to_str(), node_id];
    }

    fn variable(node_id: node_id, span: span) -> variable {
        alt self.variable_map.find(node_id) {
          some(var) {var}
          none {
            self.tcx.sess.span_bug(
                span, "No variable registered for this id");
          }
        }
    }

    fn set_captures(node_id: node_id, +cs: [capture_info]) {
        self.capture_map.insert(node_id, @cs);
    }

    fn captures(expr: @expr) -> @[capture_info] {
        alt self.capture_map.find(expr.id) {
          some(caps) {caps}
          none {
            self.tcx.sess.span_bug(expr.span, "no registered caps");
          }
        }
    }

    fn lnk(ln: live_node) -> live_node_kind {
        self.lnks[*ln]
    }

    fn add_last_use(expr_id: node_id, var: variable) {
        let v = alt self.last_use_map.find(expr_id) {
          some(v) { v }
          none {
            let v = @dvec();
            self.last_use_map.insert(expr_id, v);
            v
          }
        };
        let var_id = self.var_ids[*var];
        #debug["Node %d is a last use of variable %d", expr_id, var_id];
        (*v).push(var_id);
    }
}

fn visit_fn(fk: visit::fn_kind, decl: fn_decl, body: blk,
            sp: span, id: node_id, &&self: @ir_maps, v: vt<@ir_maps>) {
    #debug["visit_fn: id=%d", id];
    let _i = util::common::indenter();

    // swap in a new set of IR maps for this function body:
    let fn_maps = @ir_maps(self.tcx, self.method_map,
                           self.last_use_map);

    #debug["creating fn_maps: %x", ptr::addr_of(*fn_maps) as uint];

    for decl.inputs.each { |arg|
        #debug["adding argument %d", arg.id];
        (*fn_maps).add_variable(arg.id);
    }

    // gather up the various local variables, significant expressions,
    // and so forth:
    visit::visit_fn(fk, decl, body, sp, id, fn_maps, v);

    // compute liveness
    let lsets = @liveness(fn_maps);
    (*lsets).compute(body);

    // check for various error conditions
    let check_vt = visit::mk_vt(@{
        visit_fn: check_fn,
        visit_local: check_local,
        visit_expr: check_expr
        with *visit::default_visitor()
    });
    check_vt.visit_block(body, lsets, check_vt);
}

fn visit_local(local: @local, &&self: @ir_maps, vt: vt<@ir_maps>) {
    let def_map = self.tcx.def_map;
    pat_util::pat_bindings(def_map, local.node.pat) { |p_id, sp, _n|
        #debug["adding local variable %d", p_id];
        (*self).add_live_node_for_node(p_id, lnk_vdef(sp));
        (*self).add_variable(p_id);
    }
    visit::visit_local(local, self, vt);
}

fn visit_expr(expr: @expr, &&self: @ir_maps, vt: vt<@ir_maps>) {
    alt expr.node {
      // live nodes required for uses or definitions of variables:
      expr_path(_) {
        let def = self.tcx.def_map.get(expr.id);
        #debug["expr %d: path that leads to %?", expr.id, def];
        for tracked_var_id_from_def(def).each { |_id|
            (*self).add_live_node_for_node(expr.id, lnk_expr(expr.span));
        }
        visit::visit_expr(expr, self, vt);
      }
      expr_fn(_, _, _, cap_clause) |
      expr_fn_block(_, _, cap_clause) {
        // Make a live_node for each captured variable, with the span
        // being the location that the variable is used.  This results
        // in better error messages than just pointing at the closure
        // construction site.
        let proto = ty::ty_fn_proto(ty::expr_ty(self.tcx, expr));
        let cvs = capture::compute_capture_vars(self.tcx, expr.id,
                                                proto, cap_clause);
        let mut call_caps = [];
        for cvs.each { |cv|
            for tracked_var_id_from_def(cv.def).each { |n_id|
                let cv_ln = (*self).add_live_node(lnk_freevar(cv.span));
                let var = (*self).variable(n_id, cv.span);
                let is_move = alt cv.mode {
                  cap_move | cap_drop {true} // var must be dead afterwards
                  cap_copy | cap_ref {false} // var can still be used
                };
                call_caps += [{ln: cv_ln, is_move: is_move, var: var}];
            }
        }
        (*self).set_captures(expr.id, call_caps);

        visit::visit_expr(expr, self, vt);
      }

      // live nodes required for branching control flow:
      expr_if_check(*) | expr_if(*) | expr_alt(*) |
      expr_while(*) | expr_loop(*) {
        (*self).add_live_node_for_node(expr.id, lnk_expr(expr.span));
        visit::visit_expr(expr, self, vt);
      }
      expr_binary(op, _, _) if ast_util::lazy_binop(op) {
        (*self).add_live_node_for_node(expr.id, lnk_expr(expr.span));
        visit::visit_expr(expr, self, vt);
      }

      // otherwise, live nodes are not required:
      expr_index(*) | expr_field(*) | expr_vstore(*) |
      expr_vec(*) | expr_rec(*) | expr_call(*) | expr_tup(*) |
      expr_bind(*) | expr_new(*) | expr_log(*) | expr_binary(*) |
      expr_assert(*) | expr_check(*) | expr_addr_of(*) | expr_copy(*) |
      expr_loop_body(*) | expr_cast(*) | expr_unary(*) | expr_fail(*) |
      expr_ret(*) | expr_break | expr_cont | expr_lit(_) |
      expr_block(*) | expr_move(*) | expr_assign(*) | expr_swap(*) |
      expr_assign_op(*) | expr_mac(*) {
          visit::visit_expr(expr, self, vt);
      }
    }
}

// ______________________________________________________________________
// Computing liveness sets
//
// Actually we compute just a bit more than just liveness, but we use
// the same basic propagation framework in all cases.

type users = {
    reader: live_node,
    writer: live_node
};

fn invalid_users() -> users {
    {reader: invalid_node(), writer: invalid_node()}
}

class liveness {
    let tcx: ty::ctxt;
    let ir: @ir_maps;
    let successors: [mut live_node];
    let users: [mut users];
    let mut break_ln: live_node;
    let mut cont_ln: live_node;

    new(ir: @ir_maps) {
        self.ir = ir;
        self.tcx = ir.tcx;
        self.successors =
            vec::to_mut(
                vec::from_elem(self.ir.num_live_nodes,
                               invalid_node()));
        self.users =
            vec::to_mut(
                vec::from_elem(self.ir.num_live_nodes * self.ir.num_vars,
                               invalid_users()));
        self.break_ln = invalid_node();
        self.cont_ln = invalid_node();
    }

    // _______________________________________________________________________

    fn live_node(node_id: node_id, span: span) -> live_node {
        alt self.ir.live_node_map.find(node_id) {
          some(ln) {ln}
          none {
            // This must be a mismatch between the ir_map construction
            // above and the propagation code below; the two sets of
            // code have to agree about which AST nodes are worth
            // creating liveness nodes for.
            self.tcx.sess.span_bug(
                span, #fmt["No live node registered for node %d",
                           node_id]);
          }
        }
    }

    fn variable(node_id: node_id, span: span) -> variable {
        (*self.ir).variable(node_id, span)
    }

    fn variable_from_def(def: def, span: span) -> option<variable> {
        tracked_var_id_from_def(def).map { |nid|
            self.variable(nid, span)
        }
    }

    fn variable_from_def_map(node_id: node_id,
                             span: span) -> option<variable> {
        alt self.tcx.def_map.find(node_id) {
          some(def) {self.variable_from_def(def, span)}
          none {
            self.tcx.sess.span_bug(
                span, "Not present in def map")
          }
        }
    }

    fn idx(ln: live_node, var: variable) -> uint {
        *ln * self.ir.num_vars + *var
    }

    fn live_on_entry(ln: live_node, var: variable)
        -> option<live_node_kind> {

        assert ln.is_valid();
        let reader = self.users[self.idx(ln, var)].reader;
        if reader.is_valid() {some((*self.ir).lnk(reader))} else {none}
    }

    fn live_on_exit(ln: live_node, var: variable)
        -> option<live_node_kind> {

        self.live_on_entry(self.successors[*ln], var)
    }

    fn assigned_on_entry(ln: live_node, var: variable)
        -> option<live_node_kind> {

        assert ln.is_valid();
        let writer = self.users[self.idx(ln, var)].writer;
        if writer.is_valid() {some((*self.ir).lnk(writer))} else {none}
    }

    fn assigned_on_exit(ln: live_node, var: variable)
        -> option<live_node_kind> {

        self.assigned_on_entry(self.successors[*ln], var)
    }

    fn indices(ln: live_node, op: fn(uint)) {
        let node_base_idx = self.idx(ln, variable(0u));
        uint::range(0u, self.ir.num_vars) { |var_idx|
            op(node_base_idx + var_idx)
        }
    }

    fn indices2(ln: live_node, succ_ln: live_node,
                op: fn(uint, uint)) {
        let node_base_idx = self.idx(ln, variable(0u));
        let succ_base_idx = self.idx(succ_ln, variable(0u));
        uint::range(0u, self.ir.num_vars) { |var_idx|
            op(node_base_idx + var_idx, succ_base_idx + var_idx);
        }
    }

    fn write_vars(wr: io::writer,
                  ln: live_node,
                  test: fn(uint) -> live_node) {
        let node_base_idx = self.idx(ln, variable(0u));
        uint::range(0u, self.ir.num_vars) { |var_idx|
            let idx = node_base_idx + var_idx;
            if test(idx).is_valid() {
                wr.write_str(" ");
                wr.write_str(variable(var_idx).to_str());
            }
        }
    }

    fn ln_str(ln: live_node) -> str {
        io::with_str_writer { |wr|
            wr.write_str("[ln ");
            wr.write_uint(*ln);
            wr.write_str(" precedes ");
            wr.write_str(self.successors[*ln].to_str());
            wr.write_str(" live(");
            self.write_vars(wr, ln, {|idx| self.users[idx].reader});
            wr.write_str(" ) assigned(");
            self.write_vars(wr, ln, {|idx| self.users[idx].writer});
            wr.write_str(" )]");
        }
    }

    fn init_empty(ln: live_node, succ_ln: live_node) {
        self.successors[*ln] = succ_ln;

        // It is not necessary to initialize the
        // values to empty because this is the value
        // they have when they are created, and the sets
        // only grow during iterations.
        //
        // self.indices(ln) { |idx|
        //     self.users[idx] = invalid_users();
        // }
    }

    fn init_from_succ(ln: live_node, succ_ln: live_node) {
        self.successors[*ln] = succ_ln;
        self.indices2(ln, succ_ln) { |idx, succ_idx|
            self.users[idx] = self.users[succ_idx];
        }
        #debug["init_from_succ(ln=%s, succ=%s)",
               self.ln_str(ln), self.ln_str(succ_ln)];
    }

    fn merge_from_succ(ln: live_node, succ_ln: live_node) -> bool {
        if ln == succ_ln { ret false; }
        let mut changed = false;
        self.indices2(ln, succ_ln) { |idx, succ_idx|
            changed |= copy_if_invalid(self.users[succ_idx].reader,
                                       self.users[idx].reader);
            changed |= copy_if_invalid(self.users[succ_idx].writer,
                                       self.users[idx].writer);
        }
        #debug["merge_from_succ(ln=%s, succ=%s, changed=%b)",
               ln.to_str(), self.ln_str(succ_ln), changed];
        ret changed;

        fn copy_if_invalid(src: live_node, &dst: live_node) -> bool {
            if src.is_valid() {
                if !dst.is_valid() {
                    dst = src;
                    ret true;
                }
            }
            ret false;
        }
    }

    // Indicates that a local variable was *defined*; we know that no
    // uses of the variable can precede the definition (resolve checks
    // this) so we just clear out all the data.
    fn define(writer: live_node, var: variable) {
        let idx = self.idx(writer, var);
        self.users[idx].reader = invalid_node();
        self.users[idx].writer = invalid_node();

        #debug["%s defines %s", writer.to_str(), var.to_str()];
    }

    // Indicates that a new value for the local variable was assigned.
    fn write(writer: live_node, var: variable) {
        let idx = self.idx(writer, var);
        self.users[idx].reader = invalid_node();
        self.users[idx].writer = writer;

        #debug["%s writes %s", writer.to_str(), var.to_str()];
    }

    // Indicates that the current value of the local variable was used.
    fn read(reader: live_node, var: variable) {
        let idx = self.idx(reader, var);
        self.users[idx].reader = reader;

        #debug["%s reads %s", reader.to_str(), var.to_str()];
    }

    // _______________________________________________________________________

    fn compute(body: blk) {
        // if there is a `break` or `cont` at the top level, then it's
        // effectively a return---this only occurs in `for` loops,
        // where the body is really a closure.
        self.with_loop_nodes(self.ir.ret_ln, self.ir.ret_ln) {||
            self.propagate_through_block(body, self.ir.ret_ln);
        }

        // hack to skip the loop unless #debug is enabled:
        #debug["^^ liveness computation results for body %d",
               {
                   uint::range(0u, self.ir.num_live_nodes) { |ln_idx|
                       #debug["%s", self.ln_str(live_node(ln_idx))];
                   }
                   body.node.id
               }];
    }

    fn propagate_through_block(blk: blk, succ: live_node) -> live_node {
        let succ = self.propagate_through_opt_expr(blk.node.expr, succ);
        blk.node.stmts.foldr(succ) { |stmt, succ|
            self.propagate_through_stmt(stmt, succ)
        }
    }

    fn propagate_through_stmt(stmt: @stmt, succ: live_node) -> live_node {
        alt stmt.node {
          stmt_decl(decl, _) {
            ret self.propagate_through_decl(decl, succ);
          }

          stmt_expr(expr, _) | stmt_semi(expr, _) {
            ret self.propagate_through_expr(expr, succ);
          }
        }
    }

    fn propagate_through_decl(decl: @decl, succ: live_node) -> live_node {
        alt decl.node {
          decl_local(locals) {
            locals.foldr(succ) { |local, succ|
                self.propagate_through_local(local, succ)
            }
          }
          decl_item(_) {
            succ
          }
        }
    }

    fn propagate_through_local(local: @local, succ: live_node) -> live_node {
        // Note: we mark the variable as defined regardless of whether
        // there is an initializer.  Initially I had thought to only mark
        // the live variable as defined if it was initialized, and then we
        // could check for uninit variables just by scanning what is live
        // at the start of the function. But that doesn't work so well for
        // immutable variables defined in a loop:
        //     loop { let x; x = 5; }
        // because the "assignment" loops back around and generates an error.
        //
        // So now we just check that variables defined w/o an
        // initializer are not live at the point of their
        // initialization, which is mildly more complex than checking
        // once at the func header but otherwise equivalent.

        let opt_init = local.node.init.map { |i| i.expr };
        let mut succ = self.propagate_through_opt_expr(opt_init, succ);
        let def_map = self.tcx.def_map;
        pat_util::pat_bindings(def_map, local.node.pat) { |p_id, sp, _n|
            let ln = self.live_node(p_id, sp);
            let var = self.variable(p_id, sp);
            self.init_from_succ(ln, succ);
            self.define(ln, var);
            succ = ln;
        }
        succ
    }

    fn propagate_through_exprs(exprs: [@expr], succ: live_node) -> live_node {
        exprs.foldr(succ) { |expr, succ|
            self.propagate_through_expr(expr, succ)
        }
    }

    fn propagate_through_opt_expr(opt_expr: option<@expr>,
                                  succ: live_node) -> live_node {
        opt_expr.foldl(succ) { |succ, expr|
            self.propagate_through_expr(expr, succ)
        }
    }

    fn propagate_through_expr(expr: @expr, succ: live_node) -> live_node {
        alt expr.node {
          // Interesting cases with control flow or which gen/kill

          expr_path(_) {
            self.propagate_through_use_of_def(expr.id, expr.span, succ)
          }

          expr_fn(*) | expr_fn_block(*) {
            // the construction of a closure itself is not important,
            // but we have to consider the closed over variables.
            let caps = (*self.ir).captures(expr);
            (*caps).foldr(succ) { |cap, succ|
                self.init_from_succ(cap.ln, succ);
                self.read(cap.ln, cap.var);
                cap.ln
            }
          }

          expr_if_check(cond, then, els) |
          expr_if(cond, then, els) {
            let ln = self.live_node(expr.id, expr.span);
            let else_ln = self.propagate_through_opt_expr(els, succ);
            let then_ln = self.propagate_through_block(then, succ);
            self.init_from_succ(ln, else_ln);
            self.merge_from_succ(ln, then_ln);
            self.propagate_through_expr(cond, ln)
          }

          expr_while(cond, blk) {
            self.propagate_through_loop(expr, some(cond), blk, succ)
          }

          expr_loop(blk) {
            self.propagate_through_loop(expr, none, blk, succ)
          }

          expr_alt(e, arms, _) {
            let ln = self.live_node(expr.id, expr.span);
            self.init_empty(ln, succ);
            for arms.each { |arm|
                let arm_succ =
                    self.propagate_through_opt_expr(
                        arm.guard,
                        self.propagate_through_block(arm.body, succ));
                self.merge_from_succ(ln, arm_succ);
            };
            self.propagate_through_expr(e, ln)
          }

          expr_fail(o_e) | expr_ret(o_e) {
            self.propagate_through_opt_expr(o_e, self.ir.ret_ln)
          }

          expr_break {
            if !self.break_ln.is_valid() {
                self.tcx.sess.span_bug(
                    expr.span, "break with invalid break_ln");
            }

            self.break_ln
          }

          expr_cont {
            if !self.cont_ln.is_valid() {
                self.tcx.sess.span_bug(
                    expr.span, "cont with invalid cont_ln");
            }

            self.cont_ln
          }

          expr_move(l, r) | expr_assign(l, r) {
            let succ = self.write_lvalue(l, false, succ);
            let succ = self.propagate_through_expr(r, succ);
            self.propagate_through_lvalue(l, succ)
          }

          expr_swap(l, r) {
            let succ = self.write_lvalue(r, true, succ);
            let succ = self.write_lvalue(l, true, succ);
            let succ = self.propagate_through_lvalue(r, succ);
            self.propagate_through_lvalue(l, succ)
          }

          expr_assign_op(_, l, r) {
            let succ = self.write_lvalue(l, true, succ);
            let succ = self.propagate_through_expr(r, succ);
            self.propagate_through_lvalue(l, succ)
          }

          // Uninteresting cases: just propagate in rev exec order

          expr_vstore(expr, _) {
            self.propagate_through_expr(expr, succ)
          }

          expr_vec(exprs, _) {
            self.propagate_through_exprs(exprs, succ)
          }

          expr_rec(fields, with_expr) {
            let succ = self.propagate_through_opt_expr(with_expr, succ);
            fields.foldr(succ) { |field, succ|
                self.propagate_through_expr(field.node.expr, succ)
            }
          }

          expr_call(f, args, _) {
            // calling a fn with bot return type means that the fn
            // will fail, and hence the successors can be ignored
            let t_ret = ty::ty_fn_ret(ty::expr_ty(self.tcx, f));
            let succ = if ty::type_is_bot(t_ret) {self.ir.ret_ln} else {succ};
            let succ = self.propagate_through_exprs(args, succ);
            self.propagate_through_expr(f, succ)
          }

          expr_tup(exprs) {
            self.propagate_through_exprs(exprs, succ)
          }

          expr_bind(f, args) {
            let succ = args.foldr(succ) { |arg, succ|
                alt arg {
                  none {succ}
                  some(e) {self.propagate_through_expr(e, succ)}
                }
            };
            self.propagate_through_expr(f, succ)
          }

          expr_binary(op, l, r) if ast_util::lazy_binop(op) {
            let r_succ = self.propagate_through_expr(r, succ);

            let ln = self.live_node(expr.id, expr.span);
            self.init_from_succ(ln, succ);
            self.merge_from_succ(ln, r_succ);

            self.propagate_through_expr(l, ln)
          }

          expr_new(l, _, r) |
          expr_log(_, l, r) |
          expr_index(l, r) |
          expr_binary(_, l, r) {
            self.propagate_through_exprs([l, r], succ)
          }

          expr_assert(e) |
          expr_check(_, e) |
          expr_addr_of(_, e) |
          expr_field(e, _, _) |
          expr_copy(e) |
          expr_loop_body(e) |
          expr_cast(e, _) |
          expr_unary(_, e) {
            self.propagate_through_expr(e, succ)
          }

          expr_lit(*) {
            succ
          }

          expr_block(blk) {
            self.propagate_through_block(blk, succ)
          }

          expr_mac(*) {
            self.tcx.sess.span_bug(expr.span, "unexpanded macro");
          }
        }
    }

    fn propagate_through_lvalue(expr: @expr, succ: live_node) -> live_node {
        // A variable like `x` in `x = 5` is not being used.  But
        // subcomponents, like `x` in `x.f = 5`, are being used.
        alt expr.node {
          expr_path(_) { succ }

          expr_index(l, r) {
            self.propagate_through_exprs([l, r], succ)
          }

          expr_field(e, _, _) {
            self.propagate_through_expr(e, succ)
          }

          expr_unary(_, e) {
            self.propagate_through_expr(e, succ)
          }

          expr_if_check(*) | expr_if(*) | expr_while(*) |
          expr_loop(*) | expr_vstore(*) | expr_vec(*) | expr_rec(*) |
          expr_call(*) | expr_tup(*) | expr_bind(*) | expr_new(*) |
          expr_log(*) | expr_binary(*) | expr_assert(*) | expr_check(*) |
          expr_addr_of(*) | expr_copy(*) | expr_loop_body(*) | expr_cast(*) |
          expr_fail(*) | expr_ret(*) |
          expr_break | expr_cont | expr_lit(*) | expr_alt(*) |
          expr_fn(*) | expr_fn_block(*) | expr_block(*) | expr_move(*) |
          expr_assign(*) | expr_swap(*) | expr_assign_op(*) | expr_mac(*) {
            // Because we are doing this check before `borrowck`, it's
            // possible that the user has written something like
            //   3 = 5;
            // or
            //   3 <-> 5;
            // and we just haven't reported an error yet.  Just ignore
            // such invalid nonsense for now and treat it like an rvalue..
            self.propagate_through_expr(expr, succ)
          }
        }
    }

    fn write_lvalue(expr: @expr,
                    and_read: bool,
                    succ: live_node) -> live_node {
        alt expr.node {
          expr_path(_) {
            let def = self.tcx.def_map.get(expr.id);
            tracked_var_id_from_def(def).foldl(succ) { |succ, nid|
                let ln = self.live_node(expr.id, expr.span);
                self.init_from_succ(ln, succ);
                let var = self.variable(nid, expr.span);
                self.write(ln, var);

                // swaps and += write the variable, but they also read it
                if and_read { self.read(ln, var); }

                ln
            }
          }

          _ { succ }
        }
    }

    fn propagate_through_use_of_def(id: node_id,
                                    span: span,
                                    succ: live_node) -> live_node {
        let def = self.tcx.def_map.get(id);
        tracked_var_id_from_def(def).foldl(succ) { |succ, nid|
            let ln = self.live_node(id, span);
            self.init_from_succ(ln, succ);
            let var = self.variable(nid, span);
            self.read(ln, var);
            ln
        }
    }

    fn propagate_through_loop(expr: @expr,
                              cond: option<@expr>,
                              body: blk,
                              succ: live_node) -> live_node {

        /*

        We model control flow like this:

              (cond) <--+
                |       |
                v       |
          +-- (expr)    |
          |     |       |
          |     v       |
          |   (body) ---+
          |
          |
          v
        (succ)

        */

        // first iteration:
        let ln = self.live_node(expr.id, expr.span);
        self.init_empty(ln, succ);
        if cond.is_some() {
            // if there is a condition, then it's possible we bypass
            // the body altogether.  otherwise, the only way is via a
            // break in the loop body.
            self.merge_from_succ(ln, succ);
        }
        let cond_ln = self.propagate_through_opt_expr(cond, ln);
        let body_ln = self.with_loop_nodes(succ, ln) {||
            self.propagate_through_block(body, cond_ln)
        };

        // repeat until fixed point is reached:
        while self.merge_from_succ(ln, body_ln) {
            assert cond_ln == self.propagate_through_opt_expr(cond, ln);
            assert body_ln == self.with_loop_nodes(succ, ln) {||
                self.propagate_through_block(body, cond_ln)
            };
        }

        cond_ln
    }

    fn with_loop_nodes<R>(break_ln: live_node,
                          cont_ln: live_node,
                          f: fn() -> R) -> R {
        let bl = self.break_ln, cl = self.cont_ln;
        self.break_ln = break_ln;
        self.cont_ln = cont_ln;
        let r <- f();
        self.break_ln = bl;
        self.cont_ln = cl;
        ret r;
    }
}

// _______________________________________________________________________
// Checking for error conditions

fn check_local(local: @local, &&self: @liveness, vt: vt<@liveness>) {
    alt local.node.init {
      some({op: init_move, expr: expr}) {
        // can never be accessed uninitialized, but the move might
        // be invalid
        #debug["check_local() with move initializer"];
        self.check_move_from_expr(expr, vt);
      }
      some({op: init_op, expr: _}) {
        // can never be accessed uninitialized
        #debug["check_local() with initializer"];
      }
      none {
        #debug["check_local() with no initializer"];
        let def_map = self.tcx.def_map;
        pat_util::pat_bindings(def_map, local.node.pat) {|p_id, sp, _n|
            let ln = (*self).live_node(p_id, sp);
            let var = (*self).variable(p_id, sp);
            alt (*self).live_on_exit(ln, var) {
              none { /* not live: good */ }
              some(lnk) {
                self.report_illegal_read(
                    local.span,
                    lnk,
                    "variable that may not have been initialized");
              }
            }
        }
      }
    }

    visit::visit_local(local, self, vt);
}

fn check_expr(expr: @expr, &&self: @liveness, vt: vt<@liveness>) {
    alt expr.node {
      expr_path(_) {
        for (*self).variable_from_def_map(expr.id, expr.span).each { |var|
            let ln = (*self).live_node(expr.id, expr.span);
            self.consider_last_use(expr, ln, var);
        }

        visit::visit_expr(expr, self, vt);
      }

      expr_fn(_, _, _, cap_clause) | expr_fn_block(_, _, cap_clause) {
        let caps = (*self.ir).captures(expr);
        for (*caps).each { |cap|
            self.consider_last_use(expr, cap.ln, cap.var);
            if cap.is_move {
                self.check_move_from_var(expr.span, cap.ln, cap.var);
            }
        }

        visit::visit_expr(expr, self, vt);
      }

      expr_assign(l, r) {
        self.check_lvalue(l, vt);
        vt.visit_expr(r, self, vt);
      }

      expr_move(l, r) {
        self.check_lvalue(l, vt);
        self.check_move_from_expr(r, vt);
      }

      expr_call(f, args, _) {
        let targs = ty::ty_fn_args(ty::expr_ty(self.tcx, f));
        vt.visit_expr(f, self, vt);
        vec::iter2(args, targs) { |arg_expr, arg_ty|
            alt ty::resolved_mode(self.tcx, arg_ty.mode) {
              by_val | by_ref | by_mutbl_ref | by_copy {
                vt.visit_expr(arg_expr, self, vt);
              }
              by_move {
                self.check_move_from_expr(arg_expr, vt);
              }
            }
        }
      }

      // no correctness conditions related to liveness
      expr_if_check(*) | expr_if(*) | expr_alt(*) |
      expr_while(*) | expr_loop(*) |
      expr_index(*) | expr_field(*) | expr_vstore(*) |
      expr_vec(*) | expr_rec(*) | expr_tup(*) |
      expr_bind(*) | expr_new(*) | expr_log(*) | expr_binary(*) |
      expr_assert(*) | expr_check(*) | expr_addr_of(*) | expr_copy(*) |
      expr_loop_body(*) | expr_cast(*) | expr_unary(*) | expr_fail(*) |
      expr_ret(*) | expr_break | expr_cont | expr_lit(_) |
      expr_block(*) | expr_swap(*) | expr_assign_op(*) | expr_mac(*) {
        visit::visit_expr(expr, self, vt);
      }
    }
}

fn check_fn(_fk: visit::fn_kind, _decl: fn_decl,
            _body: blk, _sp: span, _id: node_id,
            &&_self: @liveness, _v: vt<@liveness>) {
    // do not check contents of nested fns
}

impl check_methods for @liveness {
    fn check_move_from_var(span: span, ln: live_node, var: variable) {
        #debug["check_move_from_var(%s, %s)",
               ln.to_str(), var.to_str()];

        alt (*self).live_on_exit(ln, var) {
          none {}
          some(lnk) {
            self.report_illegal_read(span, lnk, "moved variable");
            self.tcx.sess.span_note(
                span,
                "move of variable occurred here");
          }
        }
    }

    fn consider_last_use(expr: @expr, ln: live_node, var: variable) {
        alt (*self).live_on_exit(ln, var) {
          some(_) {}
          none {
            (*self.ir).add_last_use(expr.id, var);
          }
       }
    }

    fn check_move_from_expr(expr: @expr, vt: vt<@liveness>) {
        #debug["check_move_from_expr(node %d: %s)",
               expr.id, expr_to_str(expr)];

        if self.ir.method_map.contains_key(expr.id) {
            // actually an rvalue, since this calls a method
            ret vt.visit_expr(expr, self, vt);
        }

        alt expr.node {
          expr_path(_) {
            let def = self.tcx.def_map.get(expr.id);
            for tracked_var_id_from_def(def).each { |nid|
                // Moving from a variable is allowed if is is not live.
                let ln = (*self).live_node(expr.id, expr.span);
                let var = (*self).variable(nid, expr.span);
                self.check_move_from_var(expr.span, ln, var);
            }
          }

          expr_field(base, _, _) {
            // Moving from x.y is allowed if x is never used later.
            // (Note that the borrowck guarantees that anything
            //  being moved from is uniquely tied to the stack frame)
            self.check_move_from_expr(base, vt);
          }

          expr_index(base, idx) {
            // Moving from x[y] is allowed if x is never used later.
            // (Note that the borrowck guarantees that anything
            //  being moved from is uniquely tied to the stack frame)
            self.check_move_from_expr(base, vt);
            vt.visit_expr(idx, self, vt);
          }

          _ {
            // For other kinds of lvalues, no checks are required,
            // and any embedded expressions are actually rvalues
            vt.visit_expr(expr, self, vt);
          }
       }
    }

    fn check_lvalue(expr: @expr, vt: vt<@liveness>) {
        alt expr.node {
          expr_path(_) {
            alt self.tcx.def_map.get(expr.id) {
              def_local(nid, false) {
                // Assignment to an immutable variable or argument:
                // only legal if there is no later assignment.
                let ln = (*self).live_node(expr.id, expr.span);
                let var = (*self).variable(nid, expr.span);
                alt (*self).assigned_on_exit(ln, var) {
                  some(lnk_expr(span)) {
                    self.tcx.sess.span_err(
                        span,
                        "re-assignment of immutable variable");

                    self.tcx.sess.span_note(
                        expr.span,
                        "prior assignment occurs here");
                  }
                  some(lnk) {
                    self.tcx.sess.span_bug(
                        expr.span,
                        #fmt["illegal writer: %?", lnk]);
                   }
                  none {}
                }
              }
              def_arg(*) | def_local(_, true) {
                // Assignment to a mutable variable; no conditions
                // req'd.  In the case of arguments, the mutability is
                // enforced by borrowck.
              }
              _ {
                // Not a variable, don't care
              }
            }
          }

          _ {
            // For other kinds of lvalues, no checks are required,
            // and any embedded expressions are actually rvalues
            visit::visit_expr(expr, self, vt);
          }
       }
    }

    fn report_illegal_read(chk_span: span,
                           lnk: live_node_kind,
                           msg: str) {
        alt lnk {
          lnk_freevar(span) {
            self.tcx.sess.span_err(span, "capture of " + msg);
          }
          lnk_expr(span) {
            self.tcx.sess.span_err(span, "use of " + msg);
          }
          lnk_exit | lnk_vdef(_) {
            self.tcx.sess.span_bug(
                chk_span, #fmt["illegal reader: %?", lnk]);
          }
        }
    }
}