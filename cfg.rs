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

fn main() {
    let e = quote_expr!((), { x });
    println!("expr pre-numbering: {:s}", e.stx_to_str());
    println!("expr pre-numbering rep: {:?}", e);

    let (add_node_ids, tcx) = easy_syntax::mk_context();

    let map = mk_ast_map();
    let mut ctx = ast_map::Ctx {
        map: &map,
        parent: ast::CRATE_NODE_ID,
        fold_ops: add_node_ids
    };

    let e = ctx.fold_expr(e);
    println!("expr postnumbering: {:s}", e.stx_to_str());
    println!("expr postnumbering rep: {:?}", e);

    let method_map = @RefCell::new(nodemap::NodeMap::new());

    match e.node {
        ast::ExprBlock(b) => {
            let cfg = middle::cfg::CFG::new(tcx, method_map, b);
            println!("cfg: {:?}", cfg);
            let path = Path::new("/tmp/gviz.dot");
            let mut file = File::open_mode(&path, io::Truncate, io::Write);
            cfg::graphviz::render(&cfg, &mut file);
        }
        _ => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

