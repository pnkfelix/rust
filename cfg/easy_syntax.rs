extern crate getopts;
extern crate syntax;
extern crate rustc;

use std::cell::{Cell,RefCell};
use std::io;
// use collections::hashmap::HashMap;
use syntax::ast;
use syntax::ast_map;
use syntax::attr;
use syntax::codemap;
use syntax::diagnostic;
use syntax::parse;
use syntax::parse::token;
use syntax::print::pprust;
use rustc::driver::session;
use rustc::driver::driver;
use rustc::metadata::creader::Loader;
// use rustc::middle::lang_items::LanguageItems;
// use rustc::middle::region;
// use rustc::middle::ty;
// use rustc::util::nodemap;

// struct FoldNoOp;
// impl ast_map::FoldOps for FoldNoOp { }

#[cfg(off)]
struct AddNodeIds { sess: session::Session }

#[cfg(off)]
impl AddNodeIds {
  fn new(sess: session::Session) -> AddNodeIds { AddNodeIds { sess: sess } }
}

#[cfg(off)]
impl ast_map::FoldOps for AddNodeIds {
    fn new_id(&self, _old_id: ast::NodeId) -> ast::NodeId {
        let i = self.sess.next_node_id();
        println!("new_id: {}", i);
        i
    }
}

pub trait MkContextArg {
    fn to_crate(self) -> ast::Crate;
}

impl MkContextArg for ast::Crate {
    fn to_crate(self) -> ast::Crate { self }
}

#[cfg(off)]
impl MkContextArg for () {
    fn to_crate(self) -> ast::Crate {
        ast::Crate {
            module: ast::Mod {view_items: vec!(), items: vec!()},
            attrs: vec!(codemap::Spanned {
                node: ast::Attribute_ {
                    style: ast::AttrInner,
                    value: @codemap::Spanned {
                        node: MetaNameValue(from_str("crate_id", "easy_syntax_fake_crate")),
                        span: codemap::DUMMY_SP,
                    },
                    is_sugared_doc: false,
                },
                span: codemap::DUMMY_SP,
            }),
            config: vec!(),
            span: codemap::DUMMY_SP,
        }
    }
}

pub fn mk_context<A:MkContextArg>(arg:A) -> (session::Session,
                                             ast::Crate,
                                             ast_map::Map) {
    // fn hm<V>() -> nodemap::NodeMap<V> { nodemap::NodeMap::new() }

    let matches = getopts::getopts
        (&[~"-Z", ~"time-passes",
           ~"-Z", ~"ast-json-noexpand"],
         driver::optgroups().as_slice());
    let matches = matches.ok().unwrap();
    // println!("matches: {:?}", matches);
    let sessopts = driver::build_session_options(&matches);


    let sess = {
        // driver::build_session(sessopts, None)
        let sopts = sessopts;
        let local_crate_source_file = None;

        let codemap = @codemap::CodeMap::new();

        struct SimpleEmitter;
        impl diagnostic::Emitter for SimpleEmitter {
            fn emit(&mut self, _cmsp: Option<(&codemap::CodeMap, codemap::Span)>,
                    msg: &str, lvl: diagnostic::Level) {
                (writeln!(&mut io::stderr(), "{}: {}", lvl, msg)).unwrap();

            }
            fn custom_emit(&mut self, _cm: &codemap::CodeMap,
                           _sp: codemap::Span, msg: &str, lvl: diagnostic::Level) {
                (writeln!(&mut io::stderr(), "{}: {}", lvl, msg)).unwrap();
            }
        }
        let emitter = ~SimpleEmitter as ~diagnostic::Emitter;
        let diagnostic_handler = @diagnostic::Handler {
            err_count: Cell::new(0),
            emit: RefCell::new(emitter),
        };
        let span_diagnostic_handler =
            diagnostic::mk_span_handler(diagnostic_handler, codemap);

        driver::build_session_(sopts, local_crate_source_file, codemap, span_diagnostic_handler)
    };

    let crate_ = arg.to_crate();
    let crate_id = {
        let attrs = crate_.attrs.as_slice();
        let _crate_id_cand = match attr::first_attr_value_str_by_name(attrs, "crate_id") {
            Some(_) => (),
            None => fail!("crate in easy_syntax is supposed to have crate_id but did not"),
        };
        match attr::find_crateid(attrs) {
            Some(s) => s,
            None => fail!("easy_syntax encountered an invalid crate_id"),
        }
    };

    // let add_node_ids        = AddNodeIds::new(sess);
    // let fold_no_op          = FoldNoOp;
    // let freevars : nodemap::NodeMap<rustc::middle::freevars::freevar_info> = hm();
    // let region_paramd_items = region::resolve_crate(sess, &crate_);
    // let lang_items          = @LanguageItems::new();

    let loader = &mut Loader::new(sess);

    let (crate_, amap)      = driver::phase_2_configure_and_expand(sess,
                                                                   loader,
                                                                   crate_,
                                                                   &crate_id);
    // let (crate_, amap)      = ast_map::map_crate(crate_, add_node_ids);

    // let named_region_map    = @RefCell::new(hm());
    // let dm = @RefCell::new(HashMap::with_hasher(nodemap::FnvHasher));
    // let tcx = ty::mk_ctxt(sess, dm, named_region_map, amap, freevars, region_paramd_items, lang_items);
    (sess, crate_, amap)
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
