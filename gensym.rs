// gensym.rs

// Taken from Issue #15962

#![feature(plugin_registrar, managed_boxes, quote)]
#![crate_type = "dylib"]

extern crate syntax;
extern crate rustc;

use syntax::ast;
use syntax::codemap::{Span};
use syntax::ext::base;
use syntax::ext::base::{ExtCtxt, MacExpr};
use syntax::ext::build::AstBuilder;
use syntax::parse::token;
use rustc::plugin::Registry;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("test_quote", expand_syntax_ext);
}

pub fn expand_syntax_ext(cx: &mut ExtCtxt, sp: Span, _: &[ast::TokenTree]) -> Box<base::MacResult> {
    // expand to `{ let foo = true; foo }`, with a gensym'd foo.
    let ident = token::gensym_ident("foo");
    let decl = quote_stmt!(&mut *cx, let $ident = true;);
    let result = cx.expr_block(cx.block(sp, vec![decl], Some(cx.expr_ident(sp, ident))));

    println!("{}", result);

    MacExpr::new(result)
}

