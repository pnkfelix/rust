import core::{vec, str, option};
import option::{some, none};
import syntax::ast::*;
import syntax::visit;
import syntax::ast_util;

tag deref_t { unbox; field; index; }

type deref = @{mutbl: bool, kind: deref_t, outer_t: ty::t};

// The "root expression" is the expression that is being dereferenced in an
// assignment or a move.  For example, in the expression `a.b`, the root
// expression is `a` (or possibly `*a` if auto-derefencing is occurring).  The
// `classify_lval()` function determines whether this root is const
// (read-only) or mutable and whether or not it is movable.  A movable root is
// one that is not in the middle of a datastructure.

tag lval_classification {
    lv_deref(/*readonly:*/bool, /*kind:*/deref_t); // a.b, a[b], *a
    lv_path(def); // a::b::c
    lv_not_lvalue; // everything else
}

fn classify_lval(tcx: ty::ctxt, ex: @expr) -> lval_classification {
    fn base_ty_readonly(tcx: ty::ctxt, ty: ty::t) -> bool {
        alt ty::struct(tcx, ty) {
          ty::ty_const(_) { ret true; }
          ty::ty_box(subty) | ty::ty_ptr(subty) {
            // auto-dereference
            be base_ty_readonly(tcx, subty);
          }
          ty::ty_vec(subty) { ret false; }
          ty::ty_str. { ret true; }
          ty::ty_named(subty, _) { be base_ty_readonly(tcx, subty); }
          ty::ty_rec(_) { ret false; }
          _ { fail "Not a dereferencable type!"; }
        }
    }

    ret alt ex.node {
      expr_field(base_expr, _, _) |
      expr_index(base_expr, _) |
      expr_unary(deref., base_expr) {
        let base_ty = ty::expr_ty(tcx, base_expr);
        let kind = alt ex.node {
          expr_field(_, _, _) { field }
          expr_index(_, _) { index }
          expr_unary(_,_) { unbox }
        };
        lv_deref(base_ty_readonly(tcx, base_ty), kind)
      }

      expr_path(_) {
        let def = tcx.def_map.get(ex.id);
        lv_path(def)
      }

      _ {
        lv_not_lvalue
      }
    }
}

// Actual mutbl-checking pass

type mutbl_map = std::map::hashmap<node_id, ()>;
type ctx = {tcx: ty::ctxt, mutbl_map: mutbl_map};

fn check_crate(tcx: ty::ctxt, crate: @crate) -> mutbl_map {
    let cx = @{tcx: tcx, mutbl_map: std::map::new_int_hash()};
    let v = @{visit_expr: bind visit_expr(cx, _, _, _),
              visit_decl: bind visit_decl(cx, _, _, _)
              with *visit::default_visitor()};
    visit::visit_crate(*crate, (), visit::mk_vt(v));
    ret cx.mutbl_map;
}

tag msg { msg_assign; msg_move_out; msg_mut_ref; }

fn mk_err(cx: @ctx, span: syntax::codemap::span, msg: msg, name: str) {
    cx.tcx.sess.span_err(span, alt msg {
      msg_assign. { "assigning to " + name }
      msg_move_out. { "moving out of " + name }
      msg_mut_ref. { "passing " + name + " by mutable reference" }
    });
}

fn visit_decl(cx: @ctx, d: @decl, &&e: (), v: visit::vt<()>) {
    visit::visit_decl(d, e, v);
    alt d.node {
      decl_local(locs) {
        for (_, loc) in locs {
            alt loc.node.init {
              some(init) {
                if init.op == init_move { check_move_rhs(cx, init.expr); }
              }
              none. { }
            }
        }
      }
      _ { }
    }
}

fn visit_expr(cx: @ctx, ex: @expr, &&e: (), v: visit::vt<()>) {
    alt ex.node {
      expr_call(f, args, _) { check_call(cx, f, args); }
      expr_bind(f, args) { check_bind(cx, f, args); }
      expr_swap(lhs, rhs) {
        check_lval(cx, lhs, msg_assign);
        check_lval(cx, rhs, msg_assign);
      }
      expr_move(dest, src) {
        check_lval(cx, dest, msg_assign);
        check_move_rhs(cx, src);
      }
      expr_assign(dest, src) | expr_assign_op(_, dest, src) {
        check_lval(cx, dest, msg_assign);
      }
      _ { }
    }
    visit::visit_expr(ex, e, v);
}

fn check_lval(cx: @ctx, dest: @expr, msg: msg) {
    alt classify_lval(cx.tcx, dest) {
      lv_deref(false, _) { /* fallthrough */ }
      lv_deref(true, kind) {
        let name = alt kind {
          unbox. { "immutable box" }
          field. { "immutable field" }
          index. { "immutable vec content" }
        };
        mk_err(cx, dest.span, msg, name);
      }
      lv_path(def) {
        alt is_immutable_def(cx, def) {
          some(name) { mk_err(cx, dest.span, msg, name); }
          _ { }
        }
        cx.mutbl_map.insert(ast_util::def_id_of_def(def).node, ());
      }
      lv_not_lvalue. when msg != msg_move_out {
        mk_err(cx, dest.span, msg, "non-lvalue");
      }
      lv_not_lvalue. { /* fallthrough */ }
    }
}

fn check_move_rhs(cx: @ctx, src: @expr) {
    alt classify_lval(cx.tcx, src) {
      lv_path(def_obj_field(_, _)) {
        mk_err(cx, src.span, msg_move_out, "object field");
      }
      lv_path(def_self(_)) {
        mk_err(cx, src.span, msg_move_out, "method self");
      }
      lv_path(_) {
        check_lval(cx, src, msg_move_out);
      }
      lv_deref(_, _) {
        cx.tcx.sess.span_err(src.span, "moving out of a data structure");
      }
      lv_not_lvalue. {
        /* fallthrough */
      }
    }
}

fn check_call(cx: @ctx, f: @expr, args: [@expr]) {
    let arg_ts = ty::ty_fn_args(cx.tcx, ty::expr_ty(cx.tcx, f));
    let i = 0u;
    for arg_t: ty::arg in arg_ts {
        alt arg_t.mode {
          by_mut_ref. { check_lval(cx, args[i], msg_mut_ref); }
          by_move. { check_lval(cx, args[i], msg_move_out); }
          _ {}
        }
        i += 1u;
    }
}

fn check_bind(cx: @ctx, f: @expr, args: [option::t<@expr>]) {
    let arg_ts = ty::ty_fn_args(cx.tcx, ty::expr_ty(cx.tcx, f));
    let i = 0u;
    for arg in args {
        alt arg {
          some(expr) {
            alt (alt arg_ts[i].mode {
              by_mut_ref. { some("by mutable reference") }
              by_move. { some("by move") }
              _ { none }
            }) {
              some(name) {
                cx.tcx.sess.span_err(
                    expr.span, "can not bind an argument passed " + name);
              }
              none. {}
            }
          }
          _ {}
        }
        i += 1u;
    }
}

fn is_immutable_def(cx: @ctx, def: def) -> option::t<str> {
    alt def {
      def_fn(_, _) | def_mod(_) | def_native_mod(_) | def_const(_) |
      def_use(_) {
        some("static item")
      }
      def_arg(_, by_ref.) | def_arg(_, by_val.) |
      def_arg(_, mode_infer.) { some("argument") }
      def_obj_field(_, imm.) { some("immutable object field") }
      def_self(_) { some("self argument") }
      def_upvar(_, inner, node_id) {
        let ty = ty::node_id_to_monotype(cx.tcx, node_id);
        let proto = ty::ty_fn_proto(cx.tcx, ty);
        ret alt proto {
          proto_block. { is_immutable_def(cx, *inner) }
          _ { some("upvar") }
        };
      }
      def_binding(_) { some("binding") }
      def_local(_, let_ref.) { some("by-reference binding") }
      _ { none }
    }
}

// Local Variables:
// mode: rust
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
