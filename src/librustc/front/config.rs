// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use std::option;
use syntax::{ast, fold, attr};
use syntax::codemap::Span;

use syntax::fold::ast_fold;
use syntax::ast::*;

type in_cfg_pred = @fn(attrs: &[ast::Attribute]) -> bool;

struct Context {
    in_cfg: in_cfg_pred
}

// Support conditional compilation by transforming the AST, stripping out
// any items that do not belong in the current configuration
pub fn strip_unconfigured_items(crate: @ast::Crate) -> @ast::Crate {
    do strip_items(crate) |attrs| {
        in_cfg(crate.config, attrs)
    }
}

pub fn strip_items(crate: &ast::Crate, in_cfg: in_cfg_pred)
    -> @ast::Crate {

    let ctxt = @Context { in_cfg: in_cfg };

    let precursor = @fold::AstFoldFns {
          fold_ident: |a,b| fold_ident(ctxt, a, b),
          fold_expr: |a,b,c| fold_expr(ctxt, a, b, c),
          fold_mod: |a,b| fold_mod(ctxt, a, b),
          fold_block: |a,b| fold_block(ctxt, a, b),
          fold_foreign_mod: |a,b| fold_foreign_mod(ctxt, a, b),
          fold_item_underscore: |a,b| fold_item_underscore(ctxt, a, b),
          .. *fold::default_ast_fold()
    };

    let fold = fold::make_fold(precursor);
    @fold.fold_crate(crate)
}

fn filter_item(cx: @Context, item: @ast::item) ->
   Option<@ast::item> {
    if item_in_cfg(cx, item) { option::Some(item) } else { option::None }
}

fn filter_view_item<'r>(cx: @Context, view_item: &'r ast::view_item)-> Option<&'r ast::view_item> {
    if view_item_in_cfg(cx, view_item) {
        option::Some(view_item)
    } else {
        option::None
    }
}

fn fold_ident(_cx: @Context, i: Ident, _fld: @ast_fold) -> Ident {
    debug!("config::fold_ident: %?", i);
    i
}

fn noop_fold_expr(e: &ast::Expr_, fld: @fold::ast_fold) -> Expr_ {
    debug!("config::noop_fold_expr: %?", e);

    fn fold_field_(field: Field, fld: @ast_fold) -> Field {
        ast::Field {
            ident: fld.fold_ident(field.ident),
            expr: fld.fold_expr(field.expr),
            span: fld.new_span(field.span),
        }
    }
    let fold_field = |x| fold_field_(x, fld);

    match *e {
        ExprVstore(e, v) => {
            ExprVstore(fld.fold_expr(e), v)
        }
        ExprVec(ref exprs, mutt) => {
            ExprVec(fld.map_exprs(|x| fld.fold_expr(x), *exprs), mutt)
        }
        ExprRepeat(expr, count, mutt) => {
            ExprRepeat(fld.fold_expr(expr), fld.fold_expr(count), mutt)
        }
        ExprTup(ref elts) => ExprTup(elts.map(|x| fld.fold_expr(*x))),
        ExprCall(f, ref args, blk) => {
            ExprCall(
                fld.fold_expr(f),
                fld.map_exprs(|x| fld.fold_expr(x), *args),
                blk
            )
        }
        ExprMethodCall(callee_id, f, i, ref tps, ref args, blk) => {
            ExprMethodCall(
                fld.new_id(callee_id),
                fld.fold_expr(f),
                fld.fold_ident(i),
                tps.map(|x| fld.fold_ty(x)),
                fld.map_exprs(|x| fld.fold_expr(x), *args),
                blk
            )
        }
        ExprBinary(callee_id, binop, lhs, rhs) => {
            ExprBinary(
                fld.new_id(callee_id),
                binop,
                fld.fold_expr(lhs),
                fld.fold_expr(rhs)
            )
        }
        ExprUnary(callee_id, binop, ohs) => {
            ExprUnary(
                fld.new_id(callee_id),
                binop,
                fld.fold_expr(ohs)
            )
        }
        ExprDoBody(f) => ExprDoBody(fld.fold_expr(f)),
        ExprLit(_) => (*e).clone(),
        ExprCast(expr, ref ty) => {
            ExprCast(fld.fold_expr(expr), fld.fold_ty(ty))
        }
        ExprAddrOf(m, ohs) => ExprAddrOf(m, fld.fold_expr(ohs)),
        ExprIf(cond, ref tr, fl) => {
            ExprIf(
                fld.fold_expr(cond),
                fld.fold_block(tr),
                fl.map_move(|x| fld.fold_expr(x))
            )
        }
        ExprWhile(cond, ref body) => {
            ExprWhile(fld.fold_expr(cond), fld.fold_block(body))
        }
        ExprForLoop(pat, iter, ref body, opt_ident) => {
            ExprForLoop(fld.fold_pat(pat),
                        fld.fold_expr(iter),
                        fld.fold_block(body),
                        opt_ident.map_move(|x| fld.fold_ident(x)))
        }
        ExprLoop(ref body, opt_ident) => {
            ExprLoop(
                fld.fold_block(body),
                opt_ident.map_move(|x| fld.fold_ident(x))
            )
        }
        ExprMatch(expr, ref arms) => {
            ExprMatch(
                fld.fold_expr(expr),
                arms.map(|x| fld.fold_arm(x))
            )
        }
        ExprFnBlock(ref decl, ref body) => {
            ExprFnBlock(
                fold::fold_fn_decl(decl, fld),
                fld.fold_block(body)
            )
        }
        ExprBlock(ref blk) => ExprBlock(fld.fold_block(blk)),
        ExprAssign(el, er) => {
            ExprAssign(fld.fold_expr(el), fld.fold_expr(er))
        }
        ExprAssignOp(callee_id, op, el, er) => {
            ExprAssignOp(
                fld.new_id(callee_id),
                op,
                fld.fold_expr(el),
                fld.fold_expr(er)
            )
        }
        ExprField(el, id, ref tys) => {
            ExprField(
                fld.fold_expr(el), fld.fold_ident(id),
                tys.map(|x| fld.fold_ty(x))
            )
        }
        ExprIndex(callee_id, el, er) => {
            ExprIndex(
                fld.new_id(callee_id),
                fld.fold_expr(el),
                fld.fold_expr(er)
            )
        }
        ExprPath(ref pth) => ExprPath(fld.fold_path(pth)),
        ExprSelf => ExprSelf,
        ExprBreak(ref opt_ident) => {
            // FIXME #6993: add fold_name to fold.... then cut out the
            // bogus Name->Ident->Name conversion.
            debug!("config ExprBreak input: %?", opt_ident);
            let ret = ExprBreak(opt_ident.map_move(|x| {
                        // let i1 = Ident::new(x);
                        let i2 = fld.fold_ident(Ident::new(x));
                        i2.name
                    }));
            debug!("config ExprBreak output: %?", ret);
            ret
        }
        ExprAgain(ref opt_ident) => {
            // FIXME #6993: add fold_name to fold....
            debug!("config ExprAgain input: %?", opt_ident);
            let ret = ExprAgain(opt_ident.map_move(|x| {
                        let i1 = Ident::new(x);
                        let i2 = fld.fold_ident(i1);
                        i2.name
                    }));
            debug!("config ExprAgain output: %?", ret);
            ret
        }
        ExprRet(ref e) => {
            ExprRet(e.map_move(|x| fld.fold_expr(x)))
        }
        ExprLogLevel => ExprLogLevel,
        ExprInlineAsm(ref a) => {
            ExprInlineAsm(inline_asm {
                inputs: a.inputs.map(|&(c, input)| (c, fld.fold_expr(input))),
                outputs: a.outputs.map(|&(c, out)| (c, fld.fold_expr(out))),
                .. (*a).clone()
            })
        }
        ExprMac(ref mac) => ExprMac(fld.fold_mac(mac)),
        ExprStruct(ref path, ref fields, maybe_expr) => {
            ExprStruct(
                fld.fold_path(path),
                fields.map(|x| fold_field(*x)),
                maybe_expr.map_move(|x| fld.fold_expr(x))
            )
        },
        ExprParen(ex) => ExprParen(fld.fold_expr(ex))
    }
}


fn fold_expr(_cx: @Context, e: &ast::Expr_, s: Span, fld: @fold::ast_fold) -> (ast::Expr_, Span) {
    debug!("fold_expr: %?", e);
    fold::wrap(noop_fold_expr)(e, s, fld)
}

fn fold_mod(cx: @Context, m: &ast::_mod, fld: @fold::ast_fold) -> ast::_mod {
    debug!("fold_mod");
    let filtered_items = do  m.items.iter().filter_map |a| {
        filter_item(cx, *a).chain(|x| fld.fold_item(x))
    }.collect();
    let filtered_view_items = do m.view_items.iter().filter_map |a| {
        do filter_view_item(cx, a).map_move |x| {
            fld.fold_view_item(x)
        }
    }.collect();
    ast::_mod {
        view_items: filtered_view_items,
        items: filtered_items
    }
}

fn filter_foreign_item(cx: @Context, item: @ast::foreign_item) ->
   Option<@ast::foreign_item> {
    if foreign_item_in_cfg(cx, item) {
        option::Some(item)
    } else { option::None }
}

fn fold_foreign_mod(
    cx: @Context,
    nm: &ast::foreign_mod,
    fld: @fold::ast_fold
) -> ast::foreign_mod {
    debug!("fold_foreign_mod");
    let filtered_items = nm.items.iter().filter_map(|a| filter_foreign_item(cx, *a)).collect();
    let filtered_view_items = do nm.view_items.iter().filter_map |a| {
        do filter_view_item(cx, a).map_move |x| {
            fld.fold_view_item(x)
        }
    }.collect();
    ast::foreign_mod {
        sort: nm.sort,
        abis: nm.abis,
        view_items: filtered_view_items,
        items: filtered_items
    }
}

fn fold_item_underscore(cx: @Context, item: &ast::item_,
                        fld: @fold::ast_fold) -> ast::item_ {
    debug!("fold_item_underscore");
    let item = match *item {
        ast::item_impl(ref a, ref b, ref c, ref methods) => {
            let methods = methods.iter().filter(|m| method_in_cfg(cx, **m))
                .map(|x| *x).collect();
            ast::item_impl((*a).clone(), (*b).clone(), (*c).clone(), methods)
        }
        ast::item_trait(ref a, ref b, ref methods) => {
            let methods = methods.iter().filter(|m| trait_method_in_cfg(cx, *m) )
                .map(|x| (*x).clone()).collect();
            ast::item_trait((*a).clone(), (*b).clone(), methods)
        }
        ref item => (*item).clone(),
    };

    fold::noop_fold_item_underscore(&item, fld)
}

fn filter_stmt(cx: @Context, stmt: @ast::Stmt) ->
   Option<@ast::Stmt> {
    match stmt.node {
      ast::StmtDecl(decl, _) => {
        match decl.node {
          ast::DeclItem(item) => {
            if item_in_cfg(cx, item) {
                option::Some(stmt)
            } else { option::None }
          }
          _ => option::Some(stmt)
        }
      }
      _ => option::Some(stmt)
    }
}

fn fold_block(
    cx: @Context,
    b: &ast::Block,
    fld: @fold::ast_fold
) -> ast::Block {
    debug!("fold_block");
    let resulting_stmts = do b.stmts.iter().filter_map |a| {
        filter_stmt(cx, *a).chain(|stmt| fld.fold_stmt(stmt))
    }.collect();
    let filtered_view_items = do b.view_items.iter().filter_map |a| {
        filter_view_item(cx, a).map(|x| fld.fold_view_item(*x))
    }.collect();
    ast::Block {
        view_items: filtered_view_items,
        stmts: resulting_stmts,
        expr: b.expr.map(|x| fld.fold_expr(*x)),
        id: b.id,
        rules: b.rules,
        span: b.span,
    }
}

fn item_in_cfg(cx: @Context, item: @ast::item) -> bool {
    return (cx.in_cfg)(item.attrs);
}

fn foreign_item_in_cfg(cx: @Context, item: @ast::foreign_item) -> bool {
    return (cx.in_cfg)(item.attrs);
}

fn view_item_in_cfg(cx: @Context, item: &ast::view_item) -> bool {
    return (cx.in_cfg)(item.attrs);
}

fn method_in_cfg(cx: @Context, meth: @ast::method) -> bool {
    return (cx.in_cfg)(meth.attrs);
}

fn trait_method_in_cfg(cx: @Context, meth: &ast::trait_method) -> bool {
    match *meth {
        ast::required(ref meth) => (cx.in_cfg)(meth.attrs),
        ast::provided(@ref meth) => (cx.in_cfg)(meth.attrs)
    }
}

// Determine if an item should be translated in the current crate
// configuration based on the item's attributes
fn in_cfg(cfg: &[@ast::MetaItem], attrs: &[ast::Attribute]) -> bool {
    attr::test_cfg(cfg, attrs.iter().map(|x| *x))
}
