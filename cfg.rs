#[feature(default_type_params)];
#[feature(macro_rules)];
#[feature(managed_boxes)];
#[feature(quote)];

extern crate collections;
extern crate getopts;
extern crate syntax;
extern crate rustc;

use std::cell::RefCell;
use std::cast;
use std::io;
use std::io::{File};
use std::vec_ng::Vec;
use syntax::ast;
use syntax::ast_map;
use syntax::fold::Folder;
use rustc::middle;
use rustc::util::nodemap;
use cfg::easy_syntax;
use cfg::easy_syntax::{QuoteCtxt, SyntaxToStr};
use cfg::graphviz;

use N  = self::middle::cfg::CFGNode;
use E  = self::middle::cfg::CFGEdge;

mod cfg {
    pub mod easy_syntax;
    pub mod graphviz;
}

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

struct NamedExpr {
    name: ~str,
    expr: @syntax::ast::Expr
}

fn main() {
    let e = NamedExpr{ name: ~"just_x",
                       expr: quote_expr!((), { x }) };
    process_expr(e);
    let e = NamedExpr{ name: ~"x_t_y_e_z",
                       expr: quote_expr!((), { if x { y } else { z } }) };
    process_expr(e);
}

fn process_expr(e: NamedExpr) {
    println!("expr pre-numbering: {:s}", e.expr.stx_to_str());
    println!("expr pre-numbering rep: {:?}", e.expr);

    let (add_node_ids, tcx) = easy_syntax::mk_context();

    let map = mk_ast_map();
    let e = {
        let mut ctx = ast_map::Ctx {
            map: &map,
            parent: ast::CRATE_NODE_ID,
            fold_ops: add_node_ids
        };

        NamedExpr{ expr: ctx.fold_expr(e.expr), ..e }
    };
    println!("expr postnumbering: {:s}", e.expr.stx_to_str());
    println!("expr postnumbering rep: {:?}", e);

    let method_map = @RefCell::new(nodemap::NodeMap::new());

    match e.expr.node {
        ast::ExprBlock(b) => {
            let cfg = middle::cfg::CFG::new(tcx, method_map, b);
            println!("cfg: {:?}", cfg);
            let path = Path::new(e.name.as_slice() + ".dot");
            let mut file = File::open_mode(&path, io::Truncate, io::Write);
            let lcfg = LabelledCFG(e.name, cfg);
            match cfg::graphviz::render(&map, & &lcfg, &mut file) {
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
    cfg: middle::cfg::CFG,
}

fn LabelledCFG(label: ~str, cfg: middle::cfg::CFG) -> LabelledCFG {
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
