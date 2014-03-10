extern crate getopts;
extern crate syntax;
extern crate rustc;

use std::cell::RefCell;
use collections::hashmap::HashMap;
use syntax::ast;
use syntax::ast_map;
use syntax::codemap;
use syntax::parse;
use syntax::parse::token;
use syntax::print::pprust;
use rustc::driver::session;
use rustc::driver::driver;
use rustc::middle::lang_items::LanguageItems;
use rustc::middle::region;
use rustc::middle::ty;
use rustc::util::nodemap;

struct AddNodeIds {
    sess: session::Session
}

impl AddNodeIds {
    fn new(sess: session::Session) -> AddNodeIds { AddNodeIds { sess: sess } }
}

impl ast_map::FoldOps for AddNodeIds {
    fn new_id(&self, _old_id: ast::NodeId) -> ast::NodeId {
        let i = self.sess.next_node_id();
        println!("new_id: {}", i);
        i
    }
}

pub fn mk_context() -> (AddNodeIds, ty::ctxt) {
    fn hm<V>() -> nodemap::NodeMap<V> {
        nodemap::NodeMap::new()
    }

    let matches = getopts::getopts(&[], driver::optgroups().as_slice());
    let matches = matches.ok().unwrap();
    let sessopts = driver::build_session_options(&matches);
    let sess = driver::build_session(sessopts, None);
    let dm = @RefCell::new(HashMap::with_hasher(nodemap::FnvHasher));
    let crate_ = ast::Crate {
            module: ast::Mod {view_items: vec!(), items: vec!()},
            attrs: vec!(),
            config: vec!(),
            span: codemap::Span {
                lo: codemap::BytePos(10),
                hi: codemap::BytePos(20),
                expn_info: None,
            },
    };
    let add_node_ids        = AddNodeIds::new(sess);
    let (crate_, amap)      = ast_map::map_crate(crate_, add_node_ids);
    let freevars : nodemap::NodeMap<rustc::middle::freevars::freevar_info> = hm();
    let named_region_map    = @RefCell::new(hm());
    let region_paramd_items = region::resolve_crate(sess, &crate_);
    let lang_items          = @LanguageItems::new();

    let tcx = ty::mk_ctxt(sess, dm, named_region_map, amap, freevars,
                          region_paramd_items, lang_items);
    (add_node_ids, tcx)
}

pub trait SyntaxToStr {
    fn get_to_str() -> fn (_: &Self) -> ~str;

    fn stx_to_str(&self) -> ~str {
        SyntaxToStr::get_to_str()(self)
    }
}

macro_rules! impl_stx_to_str {
    ($Type:path, $func:path) => {
        impl SyntaxToStr for $Type {
            fn get_to_str() -> fn (_: &$Type) -> ~str {

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

pub trait QuoteCtxt {
    fn parse_sess(&self) -> @parse::ParseSess;
    fn cfg(&self) -> ast::CrateConfig;
    fn call_site(&self) -> codemap::Span;
    fn ident_of(&self, st: &str) -> ast::Ident;
}

impl QuoteCtxt for () {
    fn parse_sess(&self) -> @parse::ParseSess  { parse::new_parse_sess() }
    fn cfg(&self) -> ast::CrateConfig          { vec!() }
    fn call_site(&self) -> codemap::Span       { codemap::DUMMY_SP }
    fn ident_of(&self, st: &str) -> ast::Ident { token::str_to_ident(st) }
}
