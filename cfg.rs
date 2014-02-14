#[feature(managed_boxes)];
#[feature(quote)];
#[feature(macro_rules)];

extern mod collections;
extern mod getopts;
extern mod syntax;
extern mod rustc;

use std::cell::RefCell;
use std::hashmap::HashMap;
use collections::SmallIntMap;
use syntax::ast;
use syntax::codemap;
use syntax::parse;
use syntax::parse::token;
use syntax::print::pprust;
use rustc::driver::driver;
use rustc::middle::cfg;
use rustc::middle::lang_items::LanguageItems;
use rustc::middle::ty;

fn mk_tcx() {
    fn hm<K,V>() -> HashMap<K,V> { HashMap::new() }

    let matches = getopts::getopts(&[], &[]);
    let matches = matches.ok().unwrap();
    let sessopts = driver::build_session_options(&matches);
    let sess = driver::build_session(sessopts, None);
    let dm                  = hm();
    let amap                = hm();
    let freevars            = @RefCell::new(SmallIntMap::new());
    let region_map          = hm();
    let region_paramd_items = hm();
    let lang_items          = LanguageItems::new();

    let tcx = ty::mk_ctxt(sess, @RefCell::new(dm), @RefCell::new(amap),
                          freevars, region_map, region_paramd_items, lang_items);
    tcx
}

fn main() {
    let e = quote_expr!((), x + y);
    println!("expr: {:s}", e.to_str());

    let tcx = mk_tcx();
    let method_map = @RefCell::new(HashMap::new());

    match e.node {
        ast::ExprBlock(b) => {
            let cfg = cfg::CFG::new(tcx, method_map, b);
        }
        _            => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

trait SyntaxToStr {
    fn get_interner(&self) -> @token::IdentInterner { token::get_ident_interner() }
    fn get_to_str() -> fn (_: &Self, intr: @token::IdentInterner) -> ~str;
    fn to_str(&self) -> ~str { SyntaxToStr::get_to_str()(self, self.get_interner()) }
}

macro_rules! impl_stx_to_str {
    ($Type:path, $func:path) => {
        impl SyntaxToStr for $Type {
            fn get_to_str() -> fn (_: &$Type, intr: @token::IdentInterner) -> ~str {
                $func
            }
        }
    }
}

impl_stx_to_str!(ast::Ty,       pprust::ty_to_str)
impl_stx_to_str!(ast::Pat,      pprust::pat_to_str)
impl_stx_to_str!(ast::Expr,     pprust::expr_to_str)
impl_stx_to_str!(ast::Stmt,     pprust::stmt_to_str)
impl_stx_to_str!(ast::Item,     pprust::item_to_str)
impl_stx_to_str!(ast::Generics, pprust::generics_to_str)
impl_stx_to_str!(ast::Path,     pprust::path_to_str)

trait QuoteCtxt {
    fn parse_sess(&self) -> @syntax::parse::ParseSess;
    fn cfg(&self) -> ast::CrateConfig;
    fn call_site(&self) -> codemap::Span;
    fn ident_of(&self, st: &str) -> ast::Ident;
}

impl QuoteCtxt for () {
    fn parse_sess(&self)         -> @syntax::parse::ParseSess { parse::new_parse_sess() }
    fn cfg(&self)                -> ast::CrateConfig          { ~[] }
    fn call_site(&self)          -> codemap::Span             { codemap::DUMMY_SP }
    fn ident_of(&self, st: &str) -> ast::Ident                { token::str_to_ident(st) }
}
