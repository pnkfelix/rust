#[feature(managed_boxes)];
#[feature(quote)];
#[feature(macro_rules)];

extern mod collections;
extern mod getopts;
extern mod syntax;
extern mod rustc;

use std::cell::RefCell;
use std::hashmap::HashMap;
use diag = syntax::diagnostic;
use syntax::ast;
use syntax::ast_map;
use syntax::codemap;
use syntax::parse;
use syntax::parse::token;
use syntax::parse::token::IdentInterner;
use syntax::print::pprust;
use rustc::driver::driver;
use rustc::middle::cfg;
use rustc::middle::lang_items::LanguageItems;
use rustc::middle::region;
use rustc::middle::ty;

fn mk_tcx() -> ty::ctxt {
    struct NoFoldOps;
    impl ast_map::FoldOps for NoFoldOps { }

    fn hm<K:Eq+IterBytes,V>() -> HashMap<K,V> { HashMap::new() }
    fn ref_hm<K:Eq+IterBytes+'static,V:'static>() -> @RefCell<HashMap<K,V>> {
        @RefCell::new(hm())
    }

    let matches = getopts::getopts(&[], driver::optgroups());
    let matches = matches.ok().unwrap();
    let sessopts = driver::build_session_options(&matches);
    let sess = driver::build_session(sessopts, None);
    let dm                  = ref_hm();
    let diag                = diag::mk_span_handler(diag::mk_handler(),
                                                    @codemap::CodeMap::new());
    let crate_ = ast::Crate {
            module: ast::Mod {view_items: ~[], items: ~[]},
            attrs: ~[],
            config: ~[],
            span: codemap::Span {
                lo: codemap::BytePos(10),
                hi: codemap::BytePos(20),
                expn_info: None,
            },
        };
    let (crate_, amap)      = ast_map::map_crate(diag, crate_, NoFoldOps);
    let freevars            = hm();
    let named_region_map    = ref_hm();
    let region_paramd_items = region::resolve_crate(sess, &crate_);
    let lang_items          = @LanguageItems::new();

    let tcx = ty::mk_ctxt(sess, dm, named_region_map, amap, freevars,
                          region_paramd_items, lang_items);
    tcx
}

fn main() {
    let e = quote_expr!((), { x + y });
    println!("expr: {:s}", e.to_str());

    let tcx = mk_tcx();
    let method_map = @RefCell::new(HashMap::new());

    match e.node {
        ast::ExprBlock(b) => {
            let cfg = cfg::CFG::new(tcx, method_map, b);
            println!("cfg: {:?}", cfg);
        }
        _            => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

trait SyntaxToStr {
    fn get_to_str() -> fn (_: &Self, intr: @IdentInterner) -> ~str;

    fn get_interner(&self) -> @IdentInterner {
        token::get_ident_interner()
    }
    fn to_str(&self) -> ~str {
        SyntaxToStr::get_to_str()(self, self.get_interner())
    }
}

macro_rules! impl_stx_to_str {
    ($Type:path, $func:path) => {
        impl SyntaxToStr for $Type {
            fn get_to_str() -> fn (_: &$Type, intr: @IdentInterner) -> ~str {

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
    fn parse_sess(&self) -> @parse::ParseSess;
    fn cfg(&self) -> ast::CrateConfig;
    fn call_site(&self) -> codemap::Span;
    fn ident_of(&self, st: &str) -> ast::Ident;
}

impl QuoteCtxt for () {
    fn parse_sess(&self) -> @parse::ParseSess  { parse::new_parse_sess() }
    fn cfg(&self) -> ast::CrateConfig          { ~[] }
    fn call_site(&self) -> codemap::Span       { codemap::DUMMY_SP }
    fn ident_of(&self, st: &str) -> ast::Ident { token::str_to_ident(st) }
}
