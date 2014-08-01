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
        -> Box<MacResult> {
    // Parse an expression and emit it unchanged.
    let mut parser = parse::new_parser_from_tts(cx.parse_sess(),
        cx.cfg(), Vec::from_slice(tts));
    let expr = parser.parse_expr();
    MacExpr::new(quote_expr!(&mut *cx, $expr))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("mymacro", expand);
}
