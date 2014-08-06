#![crate_type="dylib"]
#![feature(plugin_registrar, quote, globs)]

// Taken from issue #15750

extern crate syntax;
extern crate rustc;

use rustc::plugin::Registry;

use syntax::codemap::{DUMMY_SP, Span};
use syntax::diagnostic::SpanHandler;
use syntax::ext::tt::macro_parser::{NamedMatch, MatchedSeq, MatchedNonterminal};
use syntax::ext::tt::transcribe::{TtFrame, TtReader};
use syntax::ext::tt::transcribe;
use syntax::ext::base::{ExtCtxt, MacResult, MacExpr};
use syntax::ext::quote::{id_ext};
use syntax::ext::quote;
use syntax::ext::build::AstBuilder;
use syntax::parse::token::*;
use syntax::parse::token;
use syntax::parse::lexer;
use syntax::parse;
use syntax::ast::{Ident};
use syntax::ast;

use std::collections::hashmap::HashMap;
use std::gc::Gc;
use std::rc::Rc;

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

    if false {
        let expanded = expand_parse_call(cx, _span, "parse_expr", Vec::new(), tts);
        println!("built expanded: {}", expanded);
        let manual_quote_expr_result = MacExpr::new(expanded);
        println!("built manual_quote_expr_result"); //, manual_quote_expr_result);
        let manual_quote_expr_result_expr = manual_quote_expr_result.make_expr();
        println!("manual_quote_expr_result: {}", manual_quote_expr_result_expr);
    }

    // MacExpr::new(quote_expr!(&mut *cx, $expr))
    {
        use syntax::ext::quote::rt::*;
        let ext_cx = &mut *cx;
        let parse_sess = ext_cx.parse_sess();
        let cfg = ext_cx.cfg();
        let tt = {
            let _sp = ext_cx.call_site();
            let mut tt =
                ::std::vec::Vec::new();
            tt.push_all_move(expr.to_tokens(ext_cx));
            tt
        };
        let mut parser = new_parser_from_tts(parse_sess, cfg, tt);
        let expr = parse_expr(&mut parser);
        println!("parsed: {}", expr);
        MacExpr::new(expr)
    }

}

pub fn new_parser_from_tts<'a>(sess: &'a parse::ParseSess,
                               cfg: ast::CrateConfig,
                               tts: Vec<ast::TokenTree>) -> parse::parser::Parser<'a> {
    tts_to_parser(sess, tts, cfg)
}

pub fn tts_to_parser<'a>(sess: &'a parse::ParseSess,
                         tts: Vec<ast::TokenTree>,
                         cfg: ast::CrateConfig) -> parse::parser::Parser<'a> {
    let trdr = new_tt_reader(&sess.span_diagnostic, None, tts);
    parse::parser::Parser::new(sess, cfg, box trdr)
}

/// This can do Macro-By-Example transcription. On the other hand, if
/// `src` contains no `TTSeq`s and `TTNonterminal`s, `interp` can (and
/// should) be none.
pub fn new_tt_reader<'a>(sp_diag: &'a SpanHandler,
                         interp: Option<HashMap<Ident, Rc<NamedMatch>>>,
                         src: Vec<ast::TokenTree> )
                         -> TtReader<'a> {
    let mut r = TtReader {
        sp_diag: sp_diag,
        stack: vec!(TtFrame {
            forest: Rc::new(src),
            idx: 0,
            dotdotdoted: false,
            sep: None,
        }),
        interpolations: match interp { /* just a convenience */
            None => HashMap::new(),
            Some(x) => x,
        },
        repeat_idx: Vec::new(),
        repeat_len: Vec::new(),
        /* dummy values, never read: */
        cur_tok: EOF,
        cur_span: DUMMY_SP,
    };
    transcribe::tt_next_token(&mut r); /* get cur_tok and cur_span set up */
    r
}


pub fn parse_expr(parser: &mut parse::parser::Parser) -> Gc<ast::Expr> {
    parser.parse_expr_res(parse::parser::UNRESTRICTED)
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
    println!("entered expand_parse_call: {}", tts);
    let (cx_expr, tts_expr) = expand_tts(cx, sp, tts);
    println!("expanded_tts: {}", tts_expr);

    let cfg_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, quote::id_ext("ext_cx")),
        quote::id_ext("cfg"), Vec::new());

    let parse_sess_call = || cx.expr_method_call(
        sp, cx.expr_ident(sp, quote::id_ext("ext_cx")),
        quote::id_ext("parse_sess"), Vec::new());

    let new_parser_call = {
        let id = quote::id_ext("new_parser_from_tts");
        println!("id_ext: {}", id);
        let arg2 = cx.expr_ident(sp, id);
        println!("expr_ident: {}", arg2);
        let arg3a = parse_sess_call();
        println!("parse_sess_call: {}", arg3a);
        let arg3b = cfg_call();
        println!("cfg_call: {}", arg3b);
        cx.expr_call(sp, arg2, vec!(arg3a, arg3b, tts_expr))
    };

    let expr = cx.expr_method_call(sp, new_parser_call, quote::id_ext(parse_method),
                                   arg_exprs);

    quote::expand_wrapper(cx, sp, cx_expr, expr)
}

pub fn expand_tts(cx: &ExtCtxt, sp: Span, tts: &[ast::TokenTree])
              -> (Gc<ast::Expr>, Gc<ast::Expr>) {
    println!("entered expand_tts: {}", tts);

    // NB: It appears that the main parser loses its mind if we consider
    // $foo as a TTNonterminal during the main parse, so we have to re-parse
    // under quote_depth > 0. This is silly and should go away; the _guess_ is
    // it has to do with transition away from supporting old-style macros, so
    // try removing it when enough of them are gone.

    let mut p = cx.new_parser_from_tts(tts);
    p.quote_depth += 1u;

    let cx_expr = p.parse_expr();
    println!("expand_tts parsed_expr: {}", cx_expr);

    if !p.eat(&token::COMMA) {
        p.fatal("expected token `,`");
    }

    let tts = p.parse_all_token_trees();
    p.abort_if_errors();

    // We also bind a single value, sp, to ext_cx.call_site()
    //
    // This causes every span in a token-tree quote to be attributed to the
    // call site of the extension using the quote. We can't really do much
    // better since the source of the quote may well be in a library that
    // was not even parsed by this compilation run, that the user has no
    // source code for (eg. in libsyntax, which they're just _using_).
    //
    // The old quasiquoter had an elaborate mechanism for denoting input
    // file locations from which quotes originated; unfortunately this
    // relied on feeding the source string of the quote back into the
    // compiler (which we don't really want to do) and, in any case, only
    // pushed the problem a very small step further back: an error
    // resulting from a parse of the resulting quote is still attributed to
    // the site the string literal occurred, which was in a source file
    // _other_ than the one the user has control over. For example, an
    // error in a quote from the protocol compiler, invoked in user code
    // using macro_rules! for example, will be attributed to the macro_rules.rs
    // file in libsyntax, which the user might not even have source to (unless
    // they happen to have a compiler on hand). Over all, the phase distinction
    // just makes quotes "hard to attribute". Possibly this could be fixed
    // by recreating some of the original qq machinery in the tt regime
    // (pushing fake FileMaps onto the parser to account for original sites
    // of quotes, for example) but at this point it seems not likely to be
    // worth the hassle.

    let e_sp = cx.expr_method_call(sp,
                                   cx.expr_ident(sp, id_ext("ext_cx")),
                                   id_ext("call_site"),
                                   Vec::new());

    let stmt_let_sp = cx.stmt_let(sp, false,
                                  id_ext("_sp"),
                                  e_sp);

    let stmt_let_tt = cx.stmt_let(sp, true, id_ext("tt"), cx.expr_vec_ng(sp));

    let mut vector = vec!(stmt_let_sp, stmt_let_tt);
    vector.push_all_move(quote::mk_tts(cx, sp, tts.as_slice()));
    let block = cx.expr_block(
        cx.block_all(sp,
                     Vec::new(),
                     vector,
                     Some(cx.expr_ident(sp, id_ext("tt")))));

    (cx_expr, block)
}
