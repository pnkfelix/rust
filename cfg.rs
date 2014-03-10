#[feature(managed_boxes)];
#[feature(quote)];
#[feature(macro_rules)];

extern mod collections;
extern mod getopts;
extern mod syntax;
extern mod rustc;

use std::cell::RefCell;
use std::hashmap::HashMap;
use std::cast;
use collections::SmallIntMap;
use syntax::ast;
use syntax::ast_map;
use syntax::fold::Folder;
use rustc::middle;
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
    struct MyMap { map: @RefCell<SmallIntMap<ast_map::Node>> }
    let map = MyMap { map: @RefCell::new(SmallIntMap::new()) };
    unsafe { cast::transmute(map) }
}

fn main() {
    let e = quote_expr!((), { x });
    println!("expr pre-numbering: {:s}", e.to_str());
    println!("expr pre-numbering rep: {:?}", e);

    let (add_node_ids, diag, tcx) = easy_syntax::mk_context();

    let mut ctx = ast_map::Ctx {
        map: mk_ast_map(),
        path: ~[],
        diag: diag,
        fold_ops: add_node_ids
    };

    let e = ctx.fold_expr(e);
    println!("expr postnumbering: {:s}", e.to_str());
    println!("expr postnumbering rep: {:?}", e);

    let method_map = @RefCell::new(HashMap::new());

    match e.node {
        ast::ExprBlock(b) => {
            let cfg = middle::cfg::CFG::new(tcx, method_map, b);
            println!("cfg: {:?}", cfg);
        }
        _            => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

