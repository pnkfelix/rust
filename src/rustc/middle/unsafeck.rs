import std::map::hashmap;
import syntax::ast;
import syntax::visit;
import syntax::codemap::span;
import syntax::print::pprust::expr_to_str;
import driver::session::session;

export check_crate;

type unsafeck_ctx = {tcx: ty::ctxt,
                     method_map: typeck::method_map,
                     mut unsafe_blk: bool};

fn check_crate(tcx: ty::ctxt,
               method_map: typeck::method_map,
               crate: @ast::crate) {
    let visit =
        visit::mk_vt(
            @{visit_expr: visit_expr,
              visit_block: visit_block,
              visit_fn: visit_fn
              with *visit::default_visitor()});
    let cx = {tcx: tcx, method_map: method_map, mut unsafe_blk: false};
    visit::visit_crate(*crate, cx, visit);
}

fn visit_block(blk: ast::blk, cx: unsafeck_ctx, v: visit::vt<unsafeck_ctx>) {
    let in_unsafe_blk = cx.unsafe_blk;
    alt blk.node.rules {
      ast::unsafe_blk { cx.unsafe_blk = true; }
      _ { /*pass*/ }
    }

    visit::visit_block(blk, cx, v);

    cx.unsafe_blk = in_unsafe_blk;
}

fn check_deref(cx: unsafeck_ctx, expr: @ast::expr, auto: bool) {
    let mut ty = ty::expr_ty(cx.tcx, expr);
    loop {
        alt ty::get(ty).struct {
          ty::ty_ptr(*) {
            cx.tcx.sess.span_err(
                expr.span,
                "unsafe operation requires unsafe function or block");
          }
          _ { /*pass*/ }
        }

        if !auto { ret; }
        alt ty::deref(cx.tcx, ty, !auto) {
          some(mt) { ty = mt.ty; }
          none { ret; }
        }
    }
}

fn visit_expr(expr: @ast::expr, cx: unsafeck_ctx,
              v: visit::vt<unsafeck_ctx>) {
    if !cx.unsafe_blk {
        alt expr.node {
          ast::expr_path(path) {
            alt cx.tcx.def_map.find(expr.id) {
              some(ast::def_fn(_, ast::unsafe_fn)) {
                cx.tcx.sess.span_err(
                    expr.span,
                    "unsafe fn outside of unsafe block");
              }

              _ {}
            }
          }

          ast::expr_unary(ast::deref, base) {
            check_deref(cx, base, false);
          }

          ast::expr_field(base, _, _) |
          ast::expr_index(base, _) {
            // we do not auto-dereference on method calls
            if !cx.method_map.contains_key(expr.id) {
                check_deref(cx, base, true);
            }
          }

          _ { /*ok*/ }
        }
    }

    visit::visit_expr(expr, cx, v);
}

fn visit_fn(fk: visit::fn_kind, decl: ast::fn_decl,
            body: ast::blk, sp: span,
            id: ast::node_id, cx: unsafeck_ctx,
            v: visit::vt<unsafeck_ctx>) {

    let in_unsafe_blk = cx.unsafe_blk;

    alt decl.purity {
      ast::unsafe_fn { cx.unsafe_blk = true; }
      _ { /*pass*/ }
    }

    visit::visit_fn(fk, decl, body, sp, id, cx, v);

    cx.unsafe_blk = in_unsafe_blk;
}

