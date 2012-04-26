/*

# borrowck

Checks the handling of borrows and, in general, pointers into other
data structures.  The goal is to ensure memory safety---that is, that
when a data structure has a pointer into it, that data structure is
not changed.

To achieve this effect we enforce the following rules:

- unique values which are borrowed cannot be assigned to or moved from.

- unique values can only be borrowed if there is a local path
  to the value (otherwise the previous point would be unenforcable)

- variant and dereferencing patterns cannot match on mutable memory.

# How does it work?

We visit the AST in a downward direction, maintaining a stack of borrow sets
corresponding to the current region scopes.  When a borrow of a unique value
occurs, we add the local path (LP---see next section) for the unique into the
appropriate borrow set.  Whenever we find a write or move to a local path, we
check whether it appears in the borrow set.  If so, an error is reported.

An important detail: borrowing a compound path like `a.b.c` is also considered
borrowing the subpaths `a` and `a.b`.

## Local paths

A local path (LP) encodes a path from the stack frame to the value that was
borrowed.  Each step along the path must be interior or uniquely addressed, so
given two LPs a and b, if a == b then a and b are the same data, and if a != b
then a and b cannot be the same data (that is, we need worry about aliasing).

Local paths have the following form:

    LP = x      // local variable
       | a      // argument
       | LP.f   // LP has record or unique type
       | LP[*]  // LP has unique vector type

*/

import syntax::ast;
import syntax::ast::{m_mutbl, m_imm, m_const};
import syntax::visit;
import syntax::ast_util;
import syntax::codemap::span;
import util::ppaux::ty_to_str;
import driver::session::session;
import std::map::{int_hash, hashmap, set};
import std::list;
import std::list::{list, cons, nil};
import result::{result, ok, err};
import syntax::print::pprust;

// ----------------------------------------------------------------------
// Type definitions

type ctx = @{tcx: ty::ctxt,
             method_map: typeck::method_map,
             move_set: move_set,
             mut borrows: [@local_path],
             mut defers: [@ast::expr],
             // Keep track of whether we're inside a ctor, so as to
             // allow mutating immutable fields in the same class if we
             // are in a ctor, we track the self id
             in_ctor: option<ast::node_id>};

// a set containing id's of local vars or arguments that are moved
type move_set = set<ast::node_id>;

enum local_path {
    lp_local(ast::node_id),
    lp_arg(ast::node_id),
    lp_field(@local_path, str),
    lp_index(@local_path)
}

enum what {
    borrowed(@local_path),
    not_borrowed(categorization)
}

enum msg {
    msg_assign, msg_move_out, msg_mutbl_ref, msg_imm_ref,
    msg_borrow, msg_acc
}

// ----------------------------------------------------------------------
// Visit function

fn check_crate(tcx: ty::ctxt,
               crate: @ast::crate,
               method_map: typeck::method_map) -> move_set {
    let cx = @{tcx: tcx,
               method_map: method_map,
               move_set: int_hash(),
               mut borrows: [],
               mut defers: [],
               in_ctor: none};
    let v = @{visit_expr: visit_expr,
              visit_decl: visit_decl,
              visit_item: visit_item
              with *visit::default_visitor()};
    visit::visit_crate(*crate, cx, visit::mk_vt(v));
    ret cx.move_set;
}

fn visit_decl(d: @ast::decl, &&cx: ctx, v: visit::vt<ctx>) {
    alt d.node {
      ast::decl_local(locs) {
        for locs.each {|loc|
            loc.node.init.iter {|init|
                if init.op == ast::init_move {
                    check_move_from_expr(cx, v, init.expr);
                } else {
                    check_borrowable_expr(cx, v, init.expr);
                }
            }
        }
      }
      _ {
        visit::visit_decl(d, cx, v);
      }
    }
}

fn visit_expr(ex: @ast::expr, &&cx: ctx, v: visit::vt<ctx>) {
    check_expr(cx, v, ex);
}

fn visit_item(item: @ast::item, &&cx: ctx, v: visit::vt<ctx>) {
    alt item.node {
      ast::item_class(tps, _, items, ctor, _) {
        v.visit_ty_params(tps, cx, v);
        items.iter { |i| v.visit_class_item(i, cx, v) }
        let class_cx = @{in_ctor: some(ctor.node.self_id) with *cx};
        visit::visit_class_ctor_helper(
            ctor, item.ident, tps, ast_util::local_def(item.id), class_cx, v);
      }

      _ {
        visit::visit_item(item, cx, v);
      }
    }
}

// ----------------------------------------------------------------------
// Visiting, categorizing, and checking expressions
//
// This is where the meat of the pass comes through.  The `check_expr()`
// method is the main function, though there are a few higher-level
// wrappers (e.g., `check_move_from_expr()`).
//
// check_expr() performs two tasks---
//
// 1. It checks that the expression is internally valid.
// 2. It "categorizes" the expression into one of the following kinds:
//    - rvalue
//    - lvalue living in imm/const/mut memory
//    - deinitialized path

type categorization = {acc: ast::mutability, ek: expr_kind};

enum lvalue_kind {
    lk_vec_contents,  // v[i], where v is not repesentable as a local_path
    lk_str_contents,  // s[i], where s is not repesentable as a local_path
    lk_deref,         // *p
    lk_unsafe_deref,  // *p where p is unsafe ptr
    lk_field          // p.f, where p is not representable as a local_path
}

enum expr_kind {
    // something representable by a borrow path
    ek_lp(@local_path),

    // a static item, like a fn defn
    ek_static_item(ast::def_id),

    // a reference to self
    ek_self(ast::def_id),

    // a reference to a variable
    ek_upvar(ast::node_id),

    // computed lvalues
    ek_lval(lvalue_kind),

    // an arbitrary rval (return value of a function, etc)
    ek_rval,
}

type ct = {cat: categorization, ty: ty::t};

fn check_expr(cx: ctx, v: visit::vt<ctx>,
              ex: @ast::expr) -> categorization {

    fn autoderef(cx: ctx, ct: ct) -> ct {
        alt ty::deref(cx.tcx, ct.ty) {
          some(mt) {
            let ct1 = {cat: {acc: mt.mutbl,
                             ek: ek_lval(lk_deref)},
                       ty: mt.ty};
            autoderef(cx, ct1)
          }
          none {
            ret ct;
          }
        }
    }

    fn check_expr_ty(cx: ctx, v: visit::vt<ctx>, ex: @ast::expr) -> ct {
        let ex_ty = ty::expr_ty(cx.tcx, ex);
        let ex_cat = check_expr(cx, v, ex);
        {cat: ex_cat, ty: ex_ty}
    }

    fn rval() -> categorization {
        {acc: m_imm, ek:ek_rval}
    }

    fn class_field_mutbl(cx: ctx,
                         span: span,
                         base: @ast::expr,
                         did: ast::def_id,
                         ident: str) -> ast::mutability {
        let tcx = cx.tcx;
        let in_ctor = alt cx.in_ctor {
          some(selfid) {
            alt tcx.def_map.find(base.id) {
              some(ast::def_self(slfid)) { slfid == selfid }
              _ { false }
            }
          }
          none { false }
        };
        for vec::each(ty::lookup_class_fields(tcx, did)) {|fld|
            if str::eq(ident, fld.ident) {
                alt fld.mutability {
                  ast::class_mutable { ret ast::m_mutbl; }
                  // all fields can be mutated in the ctor
                  ast::class_immutable if in_ctor { ret ast::m_mutbl; }
                  ast::class_immutable { ret ast::m_imm; }
                }
            }
        }
        tcx.sess.span_bug(span, #fmt["No class field `%s` found",
                                     ident]);
    }

    alt ex.node {
      ast::expr_path(path) {
        let def = cx.tcx.def_map.get(ex.id);
        ret check_def(cx, def);
      }

      ast::expr_field(base, ident, _) {
        let base_ct = check_expr_ty(cx, v, base);
        if cx.method_map.contains_key(ex.id) {
            ret {acc: m_imm, ek:ek_rval};
        }
        let {cat:base_cat, ty:base_ty} = {
            autoderef(cx, base_ct)
        };

        let fld_acc = {
            let fld_m = alt check ty::get(base_ty).struct {
              ty::ty_rec(fields) {
                let o_field = vec::find(fields) {|f| f.ident == ident };
                option::get(o_field).mt.mutbl
              }
              ty::ty_class(did, _tps) {
                class_field_mutbl(cx, ex.span, base, did, ident)
              }
            };
            alt fld_m {
              m_mutbl { m_mutbl }
              m_const { m_const }
              m_imm   { base_cat.acc  }
            }
        };

        let fld_ek = alt base_cat.ek {
          ek_lp(lp) { ek_lp(@lp_field(lp, ident)) }
          _ { ek_lval(lk_field) }
        };

        ret {acc: fld_acc, ek: fld_ek};
      }

      ast::expr_index(base, _) {
        let base_ct = check_expr_ty(cx, v, base);
        if cx.method_map.contains_key(ex.id) {
            ret {acc: m_imm, ek:ek_rval};
        }

        let {cat:base_cat, ty:base_ty} = autoderef(cx, base_ct);

        fn index_ek(base_ek: expr_kind, lk: lvalue_kind) -> expr_kind {
            alt base_ek {
              ek_lp(lp) { ek_lp(@lp_index(lp)) }
              _ { ek_lval(lk) }
            }
        }

        ret alt check ty::get(base_ty).struct {
          ty::ty_vec(mt) | ty::ty_evec(mt, ty::vstore_uniq) {
            {acc: mt.mutbl, ek: index_ek(base_cat.ek, lk_vec_contents)}
          }
          ty::ty_evec(mt, _) {
            {acc: mt.mutbl, ek: ek_lval(lk_vec_contents)}
          }
          ty::ty_str | ty::ty_estr(ty::vstore_uniq) {
            {acc: m_imm, ek: index_ek(base_cat.ek, lk_str_contents)}
          }
          ty::ty_estr(_) {
            {acc: m_imm, ek: ek_lval(lk_str_contents)}
          }
        };
      }

      ast::expr_unary(ast::deref, base) {
        let base_ct = check_expr_ty(cx, v, base);
        if cx.method_map.contains_key(ex.id) {
            ret {acc: m_imm, ek:ek_rval};
        }
        ret alt ty::deref(cx.tcx, base_ct.ty) {
          some(mt) {
            let lk = alt ty::get(base_ct.ty).struct {
              ty::ty_ptr(_) { lk_unsafe_deref }
              _ { lk_deref }
            };
            {acc: mt.mutbl, ek: ek_lval(lk)}
          }
          none {
            cx.tcx.sess.span_bug(
                ex.span,
                #fmt["Non-derefable type: %s",
                     ty_to_str(cx.tcx, base_ct.ty)]);
          }
        };
      }

      ast::expr_call(f, args, _) {
        check_call(cx, v, f, args);
        ret rval();
      }

      ast::expr_bind(f, args) {
        check_bind(cx, v, f, args);
        ret rval();
      }

      ast::expr_swap(lhs, rhs) {
        check_assign_to_expr(cx, v, lhs);
        check_assign_to_expr(cx, v, rhs);
        ret rval();
      }

      ast::expr_move(dest, src) {
        check_assign_to_expr(cx, v, dest);
        check_move_from_expr(cx, v, src);
        ret rval();
      }

      ast::expr_assign(dest, src) |
      ast::expr_assign_op(_, dest, src) {
        check_assign_to_expr(cx, v, dest);
        check_expr(cx, v, src);
        ret rval();
      }

      ast::expr_fn(_, _, _, cap) {
        // Note: we do not check the body here for fn expressions.
        // See check_deferred_expr() below for more details.
        for cap.moves.each {|moved|
            let def = cx.tcx.def_map.get(moved.id);
            let cat = check_def(cx, def);
            check_move_from_cat(cx, moved.span, cat);
        }
        vec::push(cx.defers, ex);
        ret rval();
      }

      ast::expr_fn_block(_, _) {
        // Note: we do not check the body here for fn expressions.
        // See check_deferred_expr() below for more details.
        vec::push(cx.defers, ex);
        ret rval();
      }

      ast::expr_addr_of(_, e) {
        // NDM a borrow occurs here
        check_expr(cx, v, e);
        ret rval();
      }

      ast::expr_assert(e) |
      ast::expr_check(_, e) |
      ast::expr_ret(some(e)) |
      ast::expr_be(e) |
      ast::expr_loop_body(e) |
      ast::expr_unary(_, e) |
      ast::expr_copy(e) |
      ast::expr_cast(e, _) |
      ast::expr_fail(some(e)) {
        check_expr(cx, v, e);
        ret rval();
      }

      ast::expr_vstore(e, _) {
        ret check_expr(cx, v, e);
      }

      ast::expr_vec(es, _) |
      ast::expr_tup(es) {
        for es.each {|e|
            check_expr(cx, v, e);
        }
        ret rval();
      }

      ast::expr_if_check(cnd, thn, els) |
      ast::expr_if(cnd, thn, els) {
        check_expr(cx, v, cnd);
        check_block(cx, v, thn);
        els.iter {|e| check_expr(cx, v, e); }
        ret rval();
      }

      ast::expr_log(_, e1, e2) |
      ast::expr_new(e1, _, e2) |
      ast::expr_binary(_, e1, e2) {
        check_expr(cx, v, e1);
        check_expr(cx, v, e2);
        ret rval();
      }

      ast::expr_while(e, b) |
      ast::expr_do_while(b, e) {
        check_expr(cx, v, e);
        check_block(cx, v, b);
        ret rval();
      }

      ast::expr_block(b) |
      ast::expr_loop(b) {
        check_block(cx, v, b);
        ret rval();
      }

      ast::expr_alt(e, arms, _) {
        check_alt(cx, v, e, arms);
        ret rval();
      }

      ast::expr_ret(none) |
      ast::expr_fail(none) |
      ast::expr_lit(_) |
      ast::expr_break |
      ast::expr_mac(_) |
      ast::expr_cont {
        /* ok */
        ret rval();
      }

      ast::expr_rec(flds, w) {
        for flds.each {|fld|
            check_expr(cx, v, fld.node.expr);
        }
        w.iter {|e|
            check_expr(cx, v, e);
        }
        ret rval();
      }
    }
}

fn check_assign_to_expr(cx: ctx, v: visit::vt<ctx>, dst: @ast::expr) {
    let cat = check_expr(cx, v, dst);
    alt cat {
      {acc: m_imm, ek: _} |
      {acc: m_const, ek: _} {
        cx.report(msg_assign, dst.span, not_borrowed(cat));
      }
      {acc: m_mut, ek: ek_lp(lp)} {
        if cx.is_borrowed(lp) {
            cx.report(msg_assign, dst.span, borrowed(lp));
        }
      }
      {acc: m_mut, ek} {
        /* ok */
      }
    }
}

fn check_move_from_expr(cx: ctx, v: visit::vt<ctx>, src: @ast::expr) {
    let cat = check_expr(cx, v, src);
    check_move_from_cat(cx, src.span, cat);
}

fn check_move_from_cat(cx: ctx, sp: span, cat: categorization) {
    fn check_move_from_var(cx: ctx, sp: span,
                           lp: @local_path, var_id: ast::node_id) {
        if cx.is_borrowed(lp) {
            cx.report(msg_move_out, sp, borrowed(lp));
        } else {
            // Find the block in which the moved variable was declared:
            cx.move_set.insert(var_id, ());
        }
    }

    alt cat {
      {acc: _, ek: ek_rval} { /* ok */ }

      {acc: _, ek: ek_lval(lk_unsafe_deref)} { /*unsafe, but ok*/ }

      // n.b.: only owned arguments can be moved.  The ownership of
      // an argument is signalled by its mutability.
      {acc: ast::m_mutbl, ek: ek_lp(lp @ @lp_arg(var_id))} |
      {acc: _, ek: ek_lp(lp @ @lp_local(var_id))} {
        check_move_from_var(cx, sp, lp, var_id);
      }

      // Note: we could eventually allow moving other `lp`, but we don't
      // today.  We'd have to extend the type state pass to work on lp's.
      {acc: _, ek: ek_lp(_)} |
      _ { // nothing else can be moved
        cx.report(msg_move_out, sp, not_borrowed(cat));
      }
    }
}

fn check_block(cx: ctx, v: visit::vt<ctx>, blk: ast::blk) {
    cx.borrow_scope(v) {||
        v.visit_block(blk, cx, v);
    }
}

fn check_alt(cx: ctx,
             v: visit::vt<ctx>,
             cond_ex: @ast::expr,
             arms: [ast::arm]) {
    cx.borrow_scope(v) {||
        check_expr(cx, v, cond_ex);
        // NDM a borrow occurs here
        for arms.each { |arm|
            v.visit_arm(arm, cx, v)
        }
    }
}

fn check_def(cx: ctx, def: ast::def) -> categorization {
    let did = ast_util::def_id_of_def(def);

    alt def {
      ast::def_fn(_, _) | ast::def_mod(_) |
      ast::def_native_mod(_) | ast::def_const(_) |
      ast::def_use(_) | ast::def_variant(_, _) |
      ast::def_ty(_) | ast::def_prim_ty(_) |
      ast::def_ty_param(_, _) | ast::def_class(_) |
      ast::def_region(_) {
        {acc: m_imm, ek: ek_static_item(did)}
      }

      ast::def_arg(_, m) {
        let acc = alt ty::resolved_mode(cx.tcx, m) {
          ast::by_ref | ast::by_val { m_imm }
          ast::by_mutbl_ref | ast::by_move | ast::by_copy { m_mutbl }
        };
        {acc: acc, ek: ek_lp(@lp_arg(did.node))}
      }

      ast::def_self(_) {
        {acc: m_imm, ek: ek_self(did)}
      }

      ast::def_upvar(_, inner, node_id) {
        let ty = ty::node_id_to_type(cx.tcx, node_id);
        let proto = ty::ty_fn_proto(ty);
        alt proto {
          ast::proto_any | ast::proto_block {
            check_def(cx, *inner)
          }
          ast::proto_bare | ast::proto_uniq | ast::proto_box {
            // FIXME #2152 allow mutation of moved upvars
            {acc: m_imm, ek: ek_upvar(did.node)}
          }
        }
      }

      // Note: we should *always* allow all local variables to be assigned
      // here and then guarantee in the typestate pass that immutable
      // local variables are assigned at most once.  But this requires a
      // new kind of propagation (def. not assigned), so I didn't do that.
      ast::def_local(_, mutbl) {
        let m = if mutbl {m_mutbl} else {m_imm};
        {acc: m, ek: ek_lp(@lp_local(did.node))}
      }

      ast::def_binding(_) {
        // no difference between a binding and any other local variable from
        // out point of view
        {acc: m_imm, ek:ek_lp(@lp_local(did.node))}
      }
    }
}

fn check_call(cx: ctx, v: visit::vt<ctx>,
              f: @ast::expr, arg_exs: [@ast::expr]) {
    check_expr(cx, v, f);
    cx.borrow_scope(v) {||
        for arg_exs.each { |arg_ex|
            check_borrowable_expr(cx, v, arg_ex);
        }
    }
}

fn check_borrowable_expr(cx: ctx, v: visit::vt<ctx>,
                         arg_ex: @ast::expr) {
    let tcx = cx.tcx;
    let cat = check_expr(cx, v, arg_ex);

    // If a borrow occurred...
    if !tcx.borrowings.contains_key(arg_ex.id) { ret; }

    // ...check what type of value was borrowed.
    let arg_ex_ty = ty::expr_ty(tcx, arg_ex);
    alt ty::get(arg_ex_ty).struct {
      ty::ty_box(_) | ty::ty_evec(_, ty::vstore_box) |
      ty::ty_estr(ty::vstore_box) {
        // Expressions of boxy types are always borrowable.  We'll just inc.
        // the ref count or keep a GC root so as to keep the thing live should
        // the variable be mutated or moved out, no biggie.
        ret;
      }

      ty::ty_uniq(_) |
      ty::ty_evec(_, ty::vstore_uniq) |
      ty::ty_estr(ty::vstore_uniq) {
        borrow_uniq_expr(cx, arg_ex.span, cat, false);
      }

      ty::ty_vec(_) | ty::ty_str {
        borrow_uniq_expr(cx, arg_ex.span, cat, true);
      }

      _ {
        tcx.sess.span_bug(
            arg_ex.span,
            #fmt["Borrowing type `%s` not handled",
                 ty_to_str(tcx, arg_ex_ty)]);
      }
    }

    fn borrow_uniq_expr(cx: ctx, span: span,
                        cat: categorization,
                        vec_str_warn: bool) {
        let lp = alt cat {
          // Local paths can always be borrowed, since we can monitor
          // those for violations.
          {acc:_, ek:ek_lp(lp)} { lp }

          // Otherwise, immutable expressions can be borrowed.  They cannot
          // be modified or moved.
          //
          // NDM -- this is not safe right now.  We might have to keep
          // some memory
          {acc:m_imm, ek:_} { ret; }

          _ if vec_str_warn {
            cx.tcx.sess.span_warn(
                span,
                #fmt["Unsafe borrowing of old-style vector/string"]);
            ret;
          }

          // Nothing else can be borrowed: we can't tell if it is modified or
          // moved out from under our feet.
          _ {
            cx.report(msg_borrow, span, not_borrowed(cat));
            ret;
          }
        };

        cx.add_borrow(lp);
    }
}

// We do not check closure bodies during check_expr().  This is because we
// need to compute the set of borrows that will be in scope when the closure
// body executes, and that information is only available once the scope which
// created the closure is removed.
//
// Consider this example:
//
//     call(a, b, c) { || expr }
//
// When the expression `expr` is evaluated, any borrows that resulted from a,
// b, or c being passed as arguments are still in scope.
//
// Therefore, what we do is to wait until popping a borrow scope before
// evaluating any closure bodies that appear within.  This is a sensible time
// because stack closures are always allocated within the innermost scope
// where they appear.  For non-stack closures (i.e., fn@, fn~) it doesn't
// actually matter when they are evaluated: they can never perform the actions
// on local variables that borrowing would prevent.
fn check_deferred_expr(cx: ctx, v: visit::vt<ctx>, ex: @ast::expr) {
    alt ex.node {
      ast::expr_fn(_, _, blk, _) |
      ast::expr_fn_block(_, blk) {
        check_block(cx, v, blk);
      }
      _ {
        cx.tcx.sess.span_bug(
            ex.span,
            #fmt["Not sure how to handle this deferred expr: %s",
                 pprust::expr_to_str(ex)]);
      }
    }
}

// ----------------------------------------------------------------------
// Helpers and so forth

impl methods for @local_path {
    fn base() -> option<@local_path> {
        alt *self {
          lp_local(_) | lp_arg(_) { none }
          lp_field(lp, _) | lp_index(lp) { some(lp) }
        }
    }
}

impl methods for ctx {
    fn borrow_scope(v: visit::vt<ctx>, f: fn()) {
        let in_borrows_len = self.borrows.len();
        let in_defers_len = self.defers.len();
        f();

        while self.defers.len() > in_defers_len {
            let deferred = vec::pop(self.defers);
            check_deferred_expr(self, v, deferred);
        }

        while self.borrows.len() > in_borrows_len {
            vec::pop(self.borrows);
        }
    }

    // Adds the path `lp` to the list of borrows paths, along with its
    // subpaths.
    fn add_borrow(lp: @local_path) {
        vec::push(self.borrows, lp);
        lp.base().iter { |lp_base|
            self.add_borrow(lp_base)
        }
    }

    // True if the path `lp` (or one of its subpaths) is borrowed.
    fn is_borrowed(lp: @local_path) -> bool {
        self.borrows.contains(lp) ||
            lp.base().map_default(false) { |b| self.is_borrowed(b) }
    }

    fn report(msg: msg, span: span, what: what) {
        fn accs(a: ast::mutability, s: str) -> str {
            let accs = alt a {
              m_imm {"immutable"}
              m_mutbl {"mutable"}
              m_const {"const"}
            };
            ret #fmt["%s %s", accs, s];
        }

        fn lp_to_str(lp: @local_path) -> str {

            // FIXME NDM --- this is rather hokey.  We should probably
            // just preserve the name of the local variables / arguments,
            // so we can say something like 'a.b.c'.

            fn base_str(lp: @local_path) -> str {
                alt *lp {
                  lp_local(_) { "local variable" }
                  lp_arg(_) { "function argument" }
                  lp_field(b, _) { base_str(b) }
                  lp_index(b) { base_str(b) }
                }
            }

            let prefix = alt *lp {
              lp_local(_) | lp_arg(_) { "" }
              lp_field(_, _) | lp_index(_) { "interior data within " }
            };

            prefix + base_str(lp)
        }

        fn cat_to_str(cat: categorization) -> str {
            alt cat {
              {acc: a, ek:ek_static_item(_)} { accs(a, "static item") }
              {acc: a, ek:ek_self(_)} { accs(a, "self reference") }
              {acc: a, ek:ek_upvar(_)} { accs(a, "upvar") }
              {acc: _, ek:ek_rval} { "non-lvalue" }
              {acc: a, ek:ek_lp(lp)} { accs(a, lp_to_str(lp)) }
              {acc: a, ek:ek_lval(lk)} {
                alt lk {
                  lk_unsafe_deref { accs(a, "unsafe deref'd value") }
                  lk_deref { accs(a, "deref'd value") }
                  lk_field { accs(a, "field") }
                  lk_str_contents { accs(a, "string contents") }
                  lk_vec_contents { accs(a, "vector contents") }
                }
              }
            }
        }

        fn what_to_str(what: what) -> str {
            alt what {
              borrowed(lp) { "borrowed " + lp_to_str(lp) }
              not_borrowed(cat) { cat_to_str(cat) }
            }
        }

        let name = what_to_str(what);
        self.tcx.sess.span_err(span, alt msg {
            msg_assign { "assigning to " + name }
            msg_move_out { "moving out of " + name }
            msg_mutbl_ref { "passing " + name + " by mutable reference" }
            msg_imm_ref { "passing " + name + " by immutable reference" }
            msg_acc { "accessing " + name }
            msg_borrow { "borrowing " + name }
        });
    }
}

// ----------------------------------------------------------------------
// Helpers and so forth

fn check_bind(cx: ctx, v: visit::vt<ctx>,
              f: @ast::expr, args: [option<@ast::expr>]) {

    let arg_ts = ty::ty_fn_args(ty::expr_ty(cx.tcx, f));
    let mut i = 0u;
    for args.each {|arg|
        alt arg {
          some(expr) {

            // FIXME NDM Surely more checks are needed here, depending
            // on the modes.

            check_expr(cx, v, expr);

            let o_msg = alt ty::resolved_mode(cx.tcx, arg_ts[i].mode) {
              ast::by_mutbl_ref { some("by mutable reference") }
              ast::by_move { some("by move") }
              _ { none }
            };

            alt o_msg {
              some(name) {
                cx.tcx.sess.span_err(
                    expr.span, "can not bind an argument passed " + name);
              }
              none {}
            }
          }
          _ {}
        }
        i += 1u;
    }
}

// Local Variables:
// mode: rust
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
