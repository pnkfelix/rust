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

// use std::cell::RefCell;
// use std::cast;
use std::io;
use std::io::{File};
use std::vec_ng::Vec;
use std::os;
use syntax::ast;
use syntax::ast_map;
use syntax::ast_util;
use syntax::codemap;
use syntax::opt_vec;
use syntax::parse::token;
use rustc::driver::driver;
// use rustc::util::nodemap;
use self::easy_syntax::{QuoteCtxt, SyntaxToStr};

use N      = self::rustc_cfg::CFGNode;
use E      = self::rustc_cfg::CFGEdge;

#[cfg(use_rustc_dataflow)]
use rustc_dataflow = rustc::middle::dataflow;
#[cfg(use_rustc_cfg)]
use rustc_cfg = rustc::middle::cfg;

#[allow(dead_code)]
#[cfg(not(use_rustc_cfg))]
mod rustc_cfg;

#[allow(dead_code)]
#[allow(deprecated_owned_vector)]
#[cfg(not(use_rustc_dataflow))]
#[path="dataflow.rs"]
mod rustc_dataflow;

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

fn setup_samples() -> Vec<Named<Expr>> {
    let mut samples = vec!();
    let e = Named::<Expr>{ name: ~"just_x",
                           val: quote_expr!((), { let x = 3; x; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"l_while_x_break_l",
                           val: quote_expr!((), {
                               let (v,w,x,y,z) = (true,(),(),(),());
                               'exit: loop { if v { w; break 'exit; x; } y }
                               z }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"if_x_then_call_y",
                           val: quote_expr!((), { let x = false; let y = ||{};
                                                  if x { y(); } }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"if_x_then_y_else_z",
                           val: quote_expr!((), { let (x,y,z) = (false,3,4);
                                                  if x { y } else { z }; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"x_send_foo_of_y",
                           val: quote_expr!((), { struct X; impl X { fn foo(&self, y: int) {} }
                                                  let (x,y) = (X,3); x.foo(y) }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"match_x",
                           val: quote_expr!((), { enum E { Foo(int), Bar(int), Baz(int) }
                                                  let (w,x,y,z1,z2,z3) = (false,Bar(3),4,5,6,7);
                                                  match x { Foo(a) => y,
                                                            Bar(b) if w => z1,
                                                            Bar(b) => z2,
                                                            Baz(c) => z3, }; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"while_x",
                           val: quote_expr!((), { let x = true;
                                                  while x {      } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_call_y",
                           val: quote_expr!((), { let x = true; let y = ||{};
                                                  while x { y(); } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_break_else_call_z",
                           val: quote_expr!((), { let x = true; let y = ||{true}; let z = ||{};
                                                  while x { if y() { break; }    z(); } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_loop_else_call_z",
                           val: quote_expr!((), { let x = true; let y = ||{false}; let z = ||{};
                                                  while x { if y() { continue; } z(); } }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"l_loop_while_v_if_w_and_x__break_l_else_call_z",
                           val: quote_expr!((), {
                               let (v,w,x,y) = (true, true, true, true);
                               let z = ||{};
                               let omega = ||{};
                               'exit: loop { while v { if w && x { break 'exit; y } z(); } }
                               omega();
                           }) };
    samples.push(e);

    samples
}

fn os_args() -> Vec<~str> {
    #[allow(deprecated_owned_vector)];
    os::args().move_iter().collect()
}

fn main() {
    let samples = setup_samples();

    let args = os_args();
    if args.len() == 1 {
        for e in samples.iter().take(1) {
            process_expr(e, BuildDataflowContext);
        }
    } else {
        assert!(args.len() > 1);
        let mut args = args; args.shift();
        while args.len() >= 2 {
            let next_args;
            match (ProcessOp::from(*args.get(0)),
                   args.get(1),
                   args.slice_from(2)) {
                (Some(op), arg, rest) => {
                    let ne = samples.iter().find(|n|n.name.as_slice() == arg.as_slice());
                    let ne = ne.unwrap_or_else(||fail!("did not find expr {}",
                                                       arg));
                    process_expr(ne, op);
                    next_args = rest.iter().map(|x|x.clone()).collect();
                }
                _ => fail!("unrecognized command line option: {}", args.get(0))
            }
            args = next_args;
        }
    }
}

fn dum_span<A>(a: A) -> codemap::Spanned<A> {
    codemap::Spanned { node: a, span: codemap::DUMMY_SP }
}

enum ProcessOp {
    BuildCFG,
    BuildDataflowContext,
}

impl ProcessOp {
    fn from(s: &str) -> Option<ProcessOp> {
        match s {
            "cfg"      => Some(BuildCFG),
            "dataflow" => Some(BuildDataflowContext),
            _          => None,
        }
    }
}

fn process_expr(e: &Named<Expr>, op: ProcessOp) {
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

    fn crate_to_expr<'a>(crate_: &'a ast::Crate) -> Expr {
        match crate_.module.items.get(0).node {
            ast::ItemFn(_, _, _, _, block) => block.expr.unwrap(),
            _ => fail!("crate does not have form expected by `process_expr`"),
        }
    }

    println!("expr pre-analysis: {:s}", e.val.stx_to_str());

    let (sess, crate_, amap) = easy_syntax::mk_context(crate_);

    let analysis = driver::phase_3_run_analysis_passes(sess,
                                                       &crate_,
                                                       amap);

    let e = Named { name: e.name.clone(), val: crate_to_expr(&crate_) };
    println!("expr postanalysis: {:s}", e.val.stx_to_str());

    match e.val.node {
        ast::ExprBlock(b) => {
            let b_named = Named{ name: e.name, val: b};
            match op {
                BuildCFG => build_cfg(analysis, b_named),
                BuildDataflowContext => build_dfc(analysis, b_named),
            }
        }
        _ => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

fn build_cfg(analysis: driver::CrateAnalysis, b: Named<ast::P<ast::Block>>) {
            let method_map = analysis.maps.method_map;
            let cfg = rustc_cfg::CFG::new(analysis.ty_cx, method_map, b.val);
            println!("cfg: {:?}", cfg);
            let path = Path::new(b.name.as_slice() + ".dot");
            let mut file = File::open_mode(&path, io::Truncate, io::Write);
            let lcfg = LabelledCFG(b.name, cfg);
            match graphviz::render(&(&analysis.ty_cx.map, &lcfg.cfg),
                                        & &lcfg, &mut file) {
                Ok(()) => println!("rendered to {}", path.display()),
                Err(err) => fail!("render failed {}", err)
            }
}

fn build_dfc(analysis: driver::CrateAnalysis, b: Named<ast::P<ast::Block>>) {
    #[deriving(Clone)]
    struct Op;
    impl rustc_dataflow::DataFlowOperator for Op {
        fn initial_value(&self) -> bool { false }
        fn join(&self, succ: uint, pred: uint) -> uint { succ | pred }
    }
    let id_range = ast_util::IdRange::max();
    let mut dfcx = rustc_dataflow::DataFlowContext::new(
        analysis.ty_cx, analysis.maps.method_map, Op, id_range, 1);
    dfcx.propagate(b.val);
}

struct LabelledCFG {
    label: ~str,
    cfg: rustc_cfg::CFG,
}

fn LabelledCFG(label: ~str, cfg: rustc_cfg::CFG) -> LabelledCFG {
    LabelledCFG{ label: label, cfg: cfg }
}

type LabelContext<'a,'b> = (&'a ast_map::Map, &'b rustc_cfg::CFG);

impl<'a,'b,'c> graphviz::Label<LabelContext<'a,'b>> for &'c LabelledCFG {
    fn name(&self, &(_c, _): &LabelContext) -> ~str {
        format!("\"{:s}\"", self.label.escape_default())
    }
}

impl<'a,'b> graphviz::Label<LabelContext<'a,'b>> for N {
    fn name(&self, _c: &LabelContext) -> ~str {
        let nodes = _c.ref1().graph.all_nodes();
        // format!("N{}", self.data.id)
        format!("N{}", nodes.iter().enumerate().find(|&(_,p)| {
            let me = self as *N;
            let curr = p as *N;
            me == curr
        }).unwrap().val0())
    }
    fn text(&self, c: &LabelContext) -> graphviz::LabelText {
        let mut s = c.ref0().node_to_str(self.data.id);
        // Replacing newlines with \\l causes each line to be left-aligned,
        // improving presentation of (long) pretty-printed expressions.
        if s.contains("\n") {
            s = s.replace("\n", "\\l");
            // Apparently left-alignment applies to line that precedes
            // \l, not line that follows; add \l at end if not already
            // present, ensuring last line left-aligned as well.
            let mut last_two : Vec<_> = s.chars().rev().take(2).collect();
            last_two.reverse();
            if last_two.as_slice() != ['\\', 'l'] {
                s.push_str("\\l");
            }
        }
        graphviz::EscStr(s)
    }
}

impl<'a,'b> graphviz::Label<LabelContext<'a,'b>> for E {
    fn name(&self, _c: &LabelContext) -> ~str {
        format!("E")
    }
    fn text(&self, c: &LabelContext) -> graphviz::LabelText {
        let mut label = ~"";
        let mut put_one = false;
        for (i, &node_id) in self.data.exiting_scopes.iter().enumerate() {
            if put_one {
                label = label + ",\\l"
            } else {
                put_one = true;
            }
            label = label + format!("exiting scope_{} {}",
                                    i, c.ref0().node_to_str(node_id));
        }
        graphviz::EscStr(label)
    }
}

impl<'a> graphviz::GraphWalk<'a, N, E> for &'a LabelledCFG {
    fn nodes(&self) -> Vec<&'a N> { self.cfg.graph.all_nodes().iter().collect() }
    fn edges(&self) -> Vec<&'a E> { self.cfg.graph.all_edges().iter().collect() }
    fn source(&self, edge:&'a E) -> &'a N {
        self.cfg.graph.node(edge.source())
    }
    fn target(&self, edge:&'a E) -> &'a N {
        self.cfg.graph.node(edge.target())
    }
}
