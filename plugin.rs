#![crate_type="dylib"]
#![feature(plugin_registrar, quote)]

// Taken from issue #15750

extern crate syntax;
extern crate rustc;

use rustc::plugin::Registry;

use syntax::codemap::Span;
use syntax::ext::base::{ExtCtxt, MacResult, MacExpr};
use syntax::parse;
use syntax::ast;

fn expand(cx: &mut ExtCtxt, _span: Span, tts: &[ast::TokenTree])
          -> Box<MacResult>
{
    // Parse an expression and emit it unchanged.
    println!("expand tts: {}", tts);
    let mut parser = parse::new_parser_from_tts(
        cx.parse_sess(), cx.cfg(), Vec::from_slice(tts));

    let expr = parser.parse_expr();
    println!("expand expr: {}", expr);

    let manual_quote_expr_result = {
        // syntax::ext::quote::expand_quote_expr(cx, _span, tts)
        let expanded = syntax::ext::quote::expand_parse_call(
            cx, _span, "parse_expr", Vec::new(), tts);
        MacExpr::new(expanded)
    };
    let manual_quote_expr_result_expr = manual_quote_expr_result.make_expr();
    println!("manual_quote_expr_result: {}", manual_quote_expr_result_expr);

    MacExpr::new(quote_expr!(&mut *cx, $expr))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("mymacro", expand);
}
