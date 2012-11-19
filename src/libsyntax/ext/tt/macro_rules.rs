use base::{ext_ctxt, mac_result, mr_expr, mr_item, mr_def, expr_tt, item_tt};
use codemap::span;
use ast::{ident, matcher_, matcher, match_tok,
             match_nonterminal, match_seq, tt_delim};
use parse::lexer::{new_tt_reader, reader};
use parse::token::{FAT_ARROW, SEMI, LBRACE, RBRACE, nt_matchers, nt_tt,
                   nt_ident};
use parse::parser::Parser;
use macro_parser::{parse, parse_or_else, success, failure, named_match,
                      matched_seq, matched_nonterminal, error};
use std::map::HashMap;
use parse::token::special_idents;
use ast_util::dummy_sp;

fn add_new_expr_extension(cx: ext_ctxt, sp: span, name: ident,
                          arg: ~[ast::token_tree]) -> mac_result {

    return add_new_extension(cx, sp, name, arg, mk_result);

    fn mk_result(cx: ext_ctxt, sp: span, name: ident,
                 lhses: ~[@named_match],
                 rhses: ~[@named_match]
                ) -> mac_result {
        let exp = |cx, sp, arg| {
            generic_extension(cx, sp, name,
                              arg, lhses, rhses,
                              |m| m,
                              |p| mr_expr(p.parse_expr()))
        };
        return mr_def({
            name: *cx.parse_sess().interner.get(name),
            ext: expr_tt({expander: exp, span: Some(sp)})
        });
    }
}

fn add_new_item_extension(cx: ext_ctxt, sp: span, name: ident,
                          arg: ~[ast::token_tree]) -> mac_result {

    return add_new_extension(cx, sp, name, arg, mk_result);

    fn mk_result(cx: ext_ctxt, sp: span, name: ident,
                 lhses: ~[@named_match],
                 rhses: ~[@named_match]
                ) -> mac_result {

        let exp = |cx: ext_ctxt, sp, name, arg| {

            let filter_matches: filter_matches = |m| {
                // This will add the binding $name to macro expansion
                let name_variable_ident =
                    cx.parse_sess().interner.intern(@~"name");
                let match_ = @matched_nonterminal(nt_ident(name, false));
                m.insert(name_variable_ident, match_);
                m
            };

            do generic_extension(cx, sp, name,
                                 arg, lhses, rhses,
                                 filter_matches) |p| {
                // XXX: Need to preserve attributes
                // on macro invocations
                let attrs = ~[];

                // XXX: Since the token tree must have braces, we're
                // going to parse a block, and insist that it only
                // contains an item. Seems hacky.
                mr_item(p.parse_item_trapped_in_block(attrs))
            }
        };
        return mr_def({
            name: *cx.parse_sess().interner.get(name),
            ext: item_tt({expander: exp, span: Some(sp)})
        });
    }
}

type mac_result_builder = &fn(cx: ext_ctxt, sp: span, name: ident,
                              lhses: ~[@named_match],
                              rhses: ~[@named_match]
                             ) -> mac_result;

fn add_new_extension(cx: ext_ctxt, sp: span, name: ident,
                     arg: ~[ast::token_tree],
                     mk_result: mac_result_builder
                    ) -> mac_result {

    // these spans won't matter, anyways
    fn ms(m: matcher_) -> matcher {
        {node: m, span: dummy_sp()}
    }

    let lhs_nm =  cx.parse_sess().interner.gensym(@~"lhs");
    let rhs_nm =  cx.parse_sess().interner.gensym(@~"rhs");

    // The grammar for macro_rules! is:
    // $( $lhs:mtcs => $rhs:tt );+
    // ...quasiquoting this would be nice.
    let argument_gram = ~[
        ms(match_seq(~[
            ms(match_nonterminal(lhs_nm, special_idents::matchers, 0u)),
            ms(match_tok(FAT_ARROW)),
            ms(match_nonterminal(rhs_nm, special_idents::tt, 1u)),
        ], Some(SEMI), false, 0u, 2u)),
        //to phase into semicolon-termination instead of
        //semicolon-separation
        ms(match_seq(~[ms(match_tok(SEMI))], None, true, 2u, 2u))];


    // Parse the macro_rules! invocation (`none` is for no interpolations):
    let arg_reader = new_tt_reader(cx.parse_sess().span_diagnostic,
                                   cx.parse_sess().interner, None, arg);
    let argument_map = parse_or_else(cx.parse_sess(), cx.cfg(),
                                     arg_reader as reader, argument_gram);

    // Extract the arguments:
    let lhses:~[@named_match] = match argument_map.get(lhs_nm) {
      @matched_seq(s, _) => s,
      _ => cx.span_bug(sp, ~"wrong-structured lhs")
    };
    let rhses:~[@named_match] = match argument_map.get(rhs_nm) {
      @matched_seq(s, _) => s,
      _ => cx.span_bug(sp, ~"wrong-structured rhs")
    };

    mk_result(cx, sp, name, lhses, rhses)
}

type filter_matches = @fn(+m: HashMap<ident, @named_match>)
    -> HashMap<ident, @named_match>;
type parse_final = @fn(&Parser) -> mac_result;

// Given `lhses` and `rhses`, this is the new macro we create
fn generic_extension(cx: ext_ctxt, sp: span, name: ident,
                     arg: ~[ast::token_tree],
                     lhses: ~[@named_match], rhses: ~[@named_match],
                     filter_matches: filter_matches,
                     parse_final: parse_final)
    -> mac_result {

    if cx.trace_macros() {
        io::println(fmt!("%s! { %s }",
                         cx.str_of(name),
                         print::pprust::tt_to_str(
                             ast::tt_delim(arg),
                             cx.parse_sess().interner)));
    }

    // Which arm's failure should we report? (the one furthest along)
    let mut best_fail_spot = dummy_sp();
    let mut best_fail_msg = ~"internal error: ran no matchers";

    let s_d = cx.parse_sess().span_diagnostic;
    let itr = cx.parse_sess().interner;

    for lhses.eachi() |i, lhs| { // try each arm's matchers
        match *lhs {
            @matched_nonterminal(nt_matchers(mtcs)) => {
                // `none` is because we're not interpolating
                let arg_rdr = new_tt_reader(s_d, itr, None, arg) as reader;
                match parse(cx.parse_sess(), cx.cfg(), arg_rdr, mtcs) {
                    success(move named_matches) => {
                        let named_matches =
                            filter_matches(move named_matches);
                        let rhs = match rhses[i] {
                            // okay, what's your transcriber?
                            @matched_nonterminal(nt_tt(@tt)) => tt,
                            _ => cx.span_bug(sp, ~"bad thing in rhs")
                        };
                        // rhs has holes ( `$id` and `$(...)` that
                        // need filled)
                        let trncbr = new_tt_reader(s_d, itr,
                                                   Some(named_matches),
                                                   ~[rhs]);
                        let p = Parser(cx.parse_sess(), cx.cfg(),
                                       trncbr as reader);
                        return parse_final(&p);
                    }
                    failure(move sp, move msg) => {
                        if sp.lo >= best_fail_spot.lo {
                            best_fail_spot = sp;
                            best_fail_msg = msg;
                        }
                    },
                    error(move sp, move msg) => cx.span_fatal(sp, msg)
                }
            }
            _ => cx.bug(~"non-matcher found in parsed lhses")
        }
    }
    cx.span_fatal(best_fail_spot, best_fail_msg);
}
