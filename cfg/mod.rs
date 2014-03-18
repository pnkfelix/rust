#[feature(default_type_params)];
#[feature(macro_rules)];
#[feature(managed_boxes)];
#[feature(quote)];
#[feature(globs)];
#[feature(phase)];

extern crate collections;
extern crate getopts;
#[phase(syntax, link)] extern crate log;
extern crate log;
extern crate rustc;
extern crate syntax;

use std::cell::RefCell;
// use std::cast;
use std::io;
use std::io::{File};
use std::vec_ng::Vec;
use syntax::ast;
use syntax::ast_map;
use syntax::codemap;
use syntax::opt_vec;
use syntax::parse::token;
use rustc::driver::driver;
use rustc::util::nodemap;
use self::easy_syntax::{QuoteCtxt, SyntaxToStr};

use N  = self::rustc_cfg::CFGNode;
use E  = self::rustc_cfg::CFGEdge;

// use rustc_cfg = rustc::middle::cfg;
#[allow(dead_code)]
mod rustc_cfg;

pub mod easy_syntax;
pub mod graphviz;

#[cfg(off)]
// TODO: add ast_map::Map::new fn, and replace this with that.
fn mk_ast_map() -> ast_map::Map {
    // Hack: work around inability to construct due to privacy in ast_map by
    // tranmuting here.
    // struct MyMap { map: @RefCell<Vec<ast_map::MapEntry>> }
    struct MyMap { map: RefCell<Vec<()>> }
    // wow will this work post transmute?  Yiles for GC.
    let map = MyMap { map: RefCell::new(Vec::new()) };
    unsafe { cast::transmute(map) }
}

type Expr = @syntax::ast::Expr;

#[deriving(Show)]
struct Named<T> {
    name: ~str,
    val: T,
}

fn main() {
    let e = Named::<Expr>{ name: ~"just_x",
                           val: quote_expr!((), { let x = 3; x; }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"l_while_x_break_l",
                           val: quote_expr!((), { let x = true;
                                                  'exit: loop { if x { break 'exit; } } }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"if_x_then_call_y",
                           val: quote_expr!((), { let x = false; let y = ||{};
                                                  if x { y(); } }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"if_x_then_y_else_z",
                           val: quote_expr!((), { let (x,y,z) = (false,3,4);
                                                  if x { y } else { z }; }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"x_send_foo_of_y",
                           val: quote_expr!((), { struct X; impl X { fn foo(&self, y: int) {} }
                                                  let (x,y) = (X,3); x.foo(y) }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"match_x",
                           val: quote_expr!((), { enum E { Foo(int), Bar(int), Baz(int) }
                                                  let (w,x,y,z1,z2,z3) = (false,Bar(3),4,5,6,7);
                                                  match x { Foo(a) => y,
                                                            Bar(b) if w => z1,
                                                            Bar(b) => z2,
                                                            Baz(c) => z3, }; }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"while_x",
                           val: quote_expr!((), { let x = true;
                                                  while x {      } }) };
    process_expr(e);
    let e = Named::<Expr>{ name: ~"while_x_call_y",
                           val: quote_expr!((), { let x = true; let y = ||{};
                                                  while x { y(); } }) };
    process_expr(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_break_else_call_z",
                           val: quote_expr!((), { let x = true; let y = ||{true}; let z = ||{};
                                                  while x { if y() { break; }    z(); } }) };
    process_expr(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_loop_else_call_z",
                           val: quote_expr!((), { let x = true; let y = ||{false}; let z = ||{};
                                                  while x { if y() { continue; } z(); } }) };
    process_expr(e);

    let e = Named::<Expr>{ name: ~"l_while_x_while_y_if_w_break_l_else_call_z",
                           val: quote_expr!((), {
                               let (w,x,y) = (true, true, true); let z = ||{};
                               'exit: loop { while y { if w && x { break 'exit; } z(); } }
                           }) };
    process_expr(e);

}

fn dum_span<A>(a: A) -> codemap::Spanned<A> {
    codemap::Spanned { node: a, span: codemap::DUMMY_SP }
}

fn process_expr(e: Named<Expr>) {
    let crate_ = {
        let fn_decl : ast::P<ast::FnDecl> = ast::P(ast::FnDecl {
            inputs: Vec::new(),
            output: ast::P(ast::Ty { id: ast::DUMMY_NODE_ID,
                                     node: ast::TyNil,
                                     span: codemap::DUMMY_SP }),
            cf: ast::Return,
            variadic: false,
        });
        let block : ast::P<ast::Block> = ast::P(ast::Block {
            view_items: vec!(),
            stmts: vec!(),
            expr: Some(e.val),
            id: ast::DUMMY_NODE_ID,
            rules: ast::DefaultBlock,
            span: codemap::DUMMY_SP,
            });
        let item : @ast::Item = @ast::Item {
            ident: ast::Ident {
                name: token::intern("main"),
                ctxt: ast::EMPTY_CTXT,
            },
            attrs: vec!(),
            id: ast::DUMMY_NODE_ID,
            node: ast::ItemFn(fn_decl, ast::ImpureFn, syntax::abi::AbiSet::Rust(),
                              ast::Generics { lifetimes: vec!(),
                                              ty_params: opt_vec::Empty },
                              block),
            vis: ast::Public,
            span: codemap::DUMMY_SP,
        };
        let mod_ : ast::Mod = ast::Mod {
            view_items: vec!(),
            items: vec!(item),
        };
        let cc : ast::CrateConfig = vec!();
        ast::Crate { module: mod_,
                     attrs: vec!(
                         dum_span(ast::Attribute_ {
                             style: ast::AttrInner,
                             value: @dum_span(ast::MetaWord(
                                 token::intern_and_get_ident("no_std"))),
                             is_sugared_doc: false,
                         }),
                         dum_span (ast::Attribute_ {
                             style: ast::AttrInner,
                             value: @dum_span(ast::MetaNameValue(
                                 token::intern_and_get_ident("crate_id"),
                                 dum_span (ast::LitStr(
                                     token::intern_and_get_ident("cfg_fake_crate"),
                                     ast::CookedStr)))),
                             is_sugared_doc: false,
                         }) ),
                     config: cc,
                     span: codemap::DUMMY_SP,
        }
    };


    println!("expr pre-analysis: {:s}", e.val.stx_to_str());
    println!("expr pre-analysis rep: {}", e.val);

    let (sess, crate_, amap) = easy_syntax::mk_context(crate_);

    println!("expr crate built rep: {}", crate_);

    let analysis = driver::phase_3_run_analysis_passes(sess,
                                                       &crate_,
                                                       amap);

    println!("expr postanalysis: {:s}", e.val.stx_to_str());
    println!("expr postanalysis: rep: {}", e);

    let method_map = @RefCell::new(nodemap::FnvHashMap::new());

    match e.val.node {
        ast::ExprBlock(b) => {
            let cfg = rustc_cfg::CFG::new(analysis.ty_cx, method_map, b);
            println!("cfg: {:?}", cfg);
            let path = Path::new(e.name.as_slice() + ".dot");
            let mut file = File::open_mode(&path, io::Truncate, io::Write);
            let lcfg = LabelledCFG(e.name, cfg);
            match graphviz::render(&analysis.ty_cx.map,
                                        & &lcfg, &mut file) {
                Ok(()) => println!("rendered to {}", path.display()),
                Err(err) => fail!("render failed {}", err)
            }
        }
        _ => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

struct LabelledCFG {
    label: ~str,
    cfg: rustc_cfg::CFG,
}

fn LabelledCFG(label: ~str, cfg: rustc_cfg::CFG) -> LabelledCFG {
    LabelledCFG{ label: label, cfg: cfg }
}

impl<'a> graphviz::Label<ast_map::Map> for &'a LabelledCFG {
    fn name(&self, _c: &ast_map::Map) -> ~str {
        format!("\"{:s}\"", self.label.escape_default())
    }
}

impl graphviz::Label<ast_map::Map> for N {
    fn name(&self, _c: &ast_map::Map) -> ~str {
        format!("N{}", self.data.id)
    }
    fn text(&self, c: &ast_map::Map) -> ~str {
        c.node_to_str(self.data.id)
    }
}

impl graphviz::Label<ast_map::Map> for E {
    fn name(&self, _c: &ast_map::Map) -> ~str {
        format!("E")
    }
    fn text(&self, c: &ast_map::Map) -> ~str {
        let mut label = ~"";
        let mut put_one = false;
        for &node_id in self.data.exiting_scopes.iter() {
            if put_one {
                label = label + ", "
            } else {
                put_one = true;
            }
            label = label + format!("{}", c.node_to_str(node_id));
        }
        label
    }
}

impl<'a> graphviz::GraphWalk<'a, N, E> for &'a LabelledCFG {
    fn nodes(&self) -> ~[&'a N] { self.cfg.graph.all_nodes().iter().collect() }
    fn edges(&self) -> ~[&'a E] { self.cfg.graph.all_edges().iter().collect() }
    fn source(&self, edge:&'a E) -> &'a N {
        self.cfg.graph.node(edge.source())
    }
    fn target(&self, edge:&'a E) -> &'a N {
        self.cfg.graph.node(edge.target())
    }
}
