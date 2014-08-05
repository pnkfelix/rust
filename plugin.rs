#![crate_type="dylib"]
#![feature(plugin_registrar, quote, globs)]

// Taken from issue #15750

extern crate syntax;
extern crate rustc;

use rustc::plugin::Registry;

use syntax::codemap::Span;
use syntax::ext::base::{ExtCtxt, MacResult, MacExpr};
use syntax::ext::base;
use syntax::ext::quote;
use syntax::ext::build::AstBuilder;
use syntax::parse::token::*;
use syntax::parse::token;
use syntax::parse;
use syntax::ast;

use std::gc::Gc;


fn expand(cx: &mut ExtCtxt, _span: Span, tts: &[ast::TokenTree])
          -> Box<MacResult>
{
    // Parse an expression and emit it unchanged.
    println!("expand tts: {}", tts);
    let mut parser = parse::new_parser_from_tts(
        cx.parse_sess(),
        cx.cfg(),
        Vec::from_slice(tts));

    let expr = parser.parse_expr();
    println!("expand expr: {}", expr);

    let expanded = expand_parse_call(cx, _span, "parse_expr", Vec::new(), tts);
    println!("built expanded: {}", expanded);
    let manual_quote_expr_result = MacExpr::new(expanded);
    println!("built manual_quote_expr_result"); //, manual_quote_expr_result);
    let manual_quote_expr_result_expr = manual_quote_expr_result.make_expr();
    println!("manual_quote_expr_result: {}", manual_quote_expr_result_expr);

    MacExpr::new(quote_expr!(&mut *cx, $expr))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("mymacro", expand);
}

pub fn expand_parse_call(cx: &ExtCtxt,
                     sp: Span,
                     parse_method: &str,
                     arg_exprs: Vec<Gc<ast::Expr>>,
                     tts: &[ast::TokenTree]) -> Gc<ast::Expr> {
    let (cx_expr, tts_expr) = quote::expand_tts(cx, sp, tts);

    let cfg_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, quote::id_ext("ext_cx")),
        quote::id_ext("cfg"), Vec::new());

    let parse_sess_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, quote::id_ext("ext_cx")),
        quote::id_ext("parse_sess"), Vec::new());

    let new_parser_call =
        cx.expr_call(sp,
                     cx.expr_ident(sp, quote::id_ext("new_parser_from_tts")),
                     vec!(parse_sess_call(), cfg_call(), tts_expr));

    let expr = cx.expr_method_call(sp, new_parser_call, quote::id_ext(parse_method),
                                   arg_exprs);

    quote::expand_wrapper(cx, sp, cx_expr, expr)
}
