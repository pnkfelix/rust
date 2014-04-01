#[feature(default_type_params)];
#[feature(macro_rules)];
#[feature(managed_boxes)];
#[feature(quote)];
#[feature(globs)];
#[feature(phase)];

extern crate arena;
extern crate collections;
extern crate getopts;
#[phase(syntax, link)] extern crate log;
extern crate log;
extern crate rustc;
extern crate syntax;

use collections::bitv::Bitv;
use std::cell;
// use std::cell::RefCell;
// use std::cast;
use std::cmp;
use std::io;
use std::io::{File};
use std::vec::Vec;
use std::os;
use syntax::abi;
use syntax::ast;
use syntax::ast_map;
// use syntax::ast_util;
use syntax::codemap;
use syntax::owned_slice::OwnedSlice;
use syntax::parse;
use syntax::parse::token;
use syntax::visit;
use syntax::visit::Visitor;
use rustc::driver::driver;
// use rustc::util::nodemap;
use self::easy_syntax::{ParseSessQC, QuoteCtxt, SyntaxToStr};

use N      = self::rustc_cfg::CFGNode;
use E      = self::rustc_cfg::CFGEdge;

use rustc_dataflow = rustc::middle::dataflow;
// use rustc_region_inference = rustc::middle::typeck::infer::region_inference;

#[cfg(use_rustc_cfg)]
use rustc_cfg = rustc::middle::cfg;

use MyOp              = self::rustc_dataflow::DataFlowOperator;
use RsOp              = self::rustc_dataflow::DataFlowOperator;

#[allow(dead_code)]
#[cfg(not(use_rustc_cfg))]
mod rustc_cfg;

#[allow(dead_code)]
#[allow(deprecated_owned_vector)]
#[path="dataflow.rs"]
mod my_dataflow;

type MyDataflowCtxt<'a, O> = my_dataflow::DataFlowContext<'a, O>;
type RsDataflowCtxt<'a, O> = rustc_dataflow::DataFlowContext<'a, O>;

trait AbstractDataFlowContext<O> {
    fn each_bit_on_entry_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool;
    fn each_bit_on_entry(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool;
    fn each_gen_bit(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool;
    fn each_gen_bit_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool;
}

impl<'a, O:MyOp> AbstractDataFlowContext<O> for MyDataflowCtxt<'a, O> {
    fn each_bit_on_entry_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_bit_on_entry_frozen(id, f)
    }
    fn each_bit_on_entry(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_bit_on_entry(id, f)
    }
    fn each_gen_bit(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_gen_bit(id, f)
    }
    fn each_gen_bit_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_gen_bit_frozen(id, f)
    }
}

impl<'a, O:RsOp> AbstractDataFlowContext<O> for RsDataflowCtxt<'a, O> {
    fn each_bit_on_entry_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_bit_on_entry_frozen(id, f)
    }
    fn each_bit_on_entry(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_bit_on_entry(id, f)
    }
    fn each_gen_bit(&mut self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_gen_bit(id, f)
    }
    fn each_gen_bit_frozen(&self, id: ast::NodeId, f: |uint| -> bool) -> bool {
        self.each_gen_bit_frozen(id, f)
    }
}

#[allow(dead_code)]
#[allow(deprecated_owned_vector)]
#[path="region_inference.rs"]
mod my_region_inference;

#[path="borrowck/mod.rs"]
mod my_borrowck;


fn make_bitvec<T>(id: ast::NodeId,
                  t: &mut T,
                  walker: |t: &mut T, f:|uint| -> bool|) -> Bitv
{
    let mut count = 0u;
    walker(t, |idx:uint| {
        debug!("node id: {} accum: {} update: {}", id, count, idx);
        count = cmp::max(idx+1, count);
        true
    });

    debug!("node id: {} count: {}", id, count);
    let mut bv = Bitv::new(count, false);
    walker(t, |idx:uint| {
        debug!("node id: {} count: {} idx: {}", id, count, idx);
        bv.set(idx, true);
        true
    });
    bv
}

fn matches_at<MyO:MyOp,
              RsO:RsOp,
              MyC: AbstractDataFlowContext<MyO>,
              RsC: AbstractDataFlowContext<RsO>>(mine: &mut MyC,
                                                 other: &mut RsC,
                                                 id: ast::NodeId) -> bool
{
    let my_bv = make_bitvec(id, mine,  |t, f| { t.each_bit_on_entry_frozen(id, f); });
    let rs_bv = make_bitvec(id, other, |t, f| { t.each_bit_on_entry_frozen(id, f); });
    if ! my_bv.equal(&rs_bv) { return false; }

    let my_bv = make_bitvec(id, mine,  |t, f| { t.each_bit_on_entry(id, f); });
    let rs_bv = make_bitvec(id, other, |t, f| { t.each_bit_on_entry(id, f); });
    if ! my_bv.equal(&rs_bv) { return false; }

    let my_bv = make_bitvec(id, mine,  |t, f| { t.each_gen_bit(id, f); });
    let rs_bv = make_bitvec(id, other, |t, f| { t.each_gen_bit(id, f); });
    if ! my_bv.equal(&rs_bv) { return false; }

    let my_bv = make_bitvec(id, mine,  |t, f| { t.each_gen_bit_frozen(id, f); });
    let rs_bv = make_bitvec(id, other, |t, f| { t.each_gen_bit_frozen(id, f); });
    if ! my_bv.equal(&rs_bv) { return false; }

    return true;
}

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

#[deriving(Clone,Show)]
struct Named<T> {
    name: ~str,
    val: T,
}

impl<T> Named<T> {
    fn map<U>(self, f: |T| -> U) -> Named<U> {
        let Named { name, val } = self;
        Named { name: name, val: f(val) }
    }
    fn map_ref<'a, U>(&'a self, f: |&'a T| -> U) -> Named<U> {
        Named { name: self.name.clone(), val: f(&self.val) }
    }
}

fn setup_samples(sess: parse::ParseSess) -> Vec<Named<Expr>> {
    let ref ps = ParseSessQC(sess);
    let mut samples = vec!();
    let e = Named::<Expr>{ name: ~"just_x",
                           val: quote_expr!(ps, { let x = 3; x; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"l_while_x_break_l",
                           val: quote_expr!(ps, {
                               let (v,w,x,y,z) = (true,(),(),(),());
                               'exit: loop { if v { w; break 'exit; x; } y }
                               z }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"if_x_then_call_y",
                           val: quote_expr!(ps, { let x = false; let y = ||{};
                                                  if x { y(); } }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"if_x_then_y_else_z",
                           val: quote_expr!(ps, { let (x,y,z) = (false,3,4);
                                                  if x { y } else { z }; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"x_send_foo_of_y",
                           val: quote_expr!(ps, { struct X; impl X { fn foo(&self, y: int) {} }
                                                  let (x,y) = (X,3); x.foo(y) }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"match_x",
                           val: quote_expr!(ps, { enum E { Foo(int), Bar(int), Baz(int) }
                                                  let (w,x,y,z1,z2,z3) = (false,Bar(3),4,5,6,7);
                                                  match x { Foo(a) => y,
                                                            Bar(b) if w => z1,
                                                            Bar(b) => z2,
                                                            Baz(c) => z3, }; }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"while_x",
                           val: quote_expr!(ps, { let x = true;
                                                  while x {      } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_call_y",
                           val: quote_expr!(ps, { let x = true; let y = ||{};
                                                  while x { y(); } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_break_else_call_z",
                           val: quote_expr!(ps, { let x = true; let y = ||{true}; let z = ||{};
                                                  while x { if y() { break; }    z(); } }) };
    samples.push(e);
    let e = Named::<Expr>{ name: ~"while_x_if_call_y_loop_else_call_z",
                           val: quote_expr!(ps, { let x = true; let y = ||{false}; let z = ||{};
                                                  while x { if y() { continue; } z(); } }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"l_loop_while_v_if_w_and_x__break_l_else_call_z",
                           val: quote_expr!(ps, {
                               let (v,w,x,y) = (true, true, true, true);
                               let z = ||{};
                               let omega = ||{};
                               'exit: loop { while v { if w && x { break 'exit; y } z(); } }
                               omega();
                           }) };
    samples.push(e);

    let e = Named::<Expr>{ name: ~"l_loop_while_v_bw_if_w_and_x_by_break_l_else_call_z",
                           val: quote_expr!(ps, {
                               let (v,w,x,y) = (true, true, true, true);
                               let b = |a|{};
                               let z = ||{};
                               let omega = ||{};
                               'exit: loop { while v {
                                   b(&w); if w && x { b(&y); break 'exit; y } z();
                               } }
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
    let samples = setup_samples(parse::new_parse_sess());

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
    BuildRegionInferenceGraph,
    GatherLoans,
}

impl ProcessOp {
    fn from(s: &str) -> Option<ProcessOp> {
        match s {
            "cfg"      => Some(BuildCFG),
            "dataflow" => Some(BuildDataflowContext),
            "region_inference" => Some(BuildRegionInferenceGraph),
            "loans"    => Some(GatherLoans),
            _          => None,
        }
    }
}

fn expr_to_crate(e: Expr) -> ast::Crate {
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
        expr: Some(e),
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
        node: ast::ItemFn(fn_decl, ast::ImpureFn, abi::AbiSet::Rust(),
                          ast::Generics { lifetimes: vec!(),
                                          ty_params: OwnedSlice::empty(), },
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
}

fn crate_to_decl_block<'a>(crate_: ast::Crate) -> (ast::Ident,
                                                   ast::Purity,
                                                   @ast::FnDecl,
                                                   abi::AbiSet,
                                                   ast::Generics,
                                                   @ast::Block) {
    let item = crate_.module.items.get(0);
    match item.node.clone() {
        ast::ItemFn(decl, purity, abi, generics, block)
            => (item.ident, purity, decl, abi, generics, block),
        _ => fail!("crate does not have form expected by `process_expr`"),
    }
}

fn crate_to_expr<'a>(crate_: ast::Crate) -> Expr {
    let (_, _, _, _, _, b) = crate_to_decl_block(crate_);
    b.expr.unwrap()
}

fn process_expr(e: &Named<Expr>, op: ProcessOp) {
    println!("expr pre-analysis: {:s}", e.val.stx_to_str());

    let crate_ = e.clone().map(expr_to_crate);

    let (sess, crate_, amap) = {
        let Named { name, val } = crate_;
        let sess = easy_syntax::mk_sess();
        let (crate_, amap) = easy_syntax::mk_context(val, &sess);
        (sess, Named{ name: name, val: crate_ }, amap)
    };

    let analysis = driver::phase_3_run_analysis_passes(sess,
                                                       &crate_.val,
                                                       amap);

    println!("expr postanalysis: {:s}", crate_to_expr(crate_.val.clone()).stx_to_str());

    match crate_to_expr(crate_.val.clone()).node {
        ast::ExprBlock(b) => {
            match op {
                BuildCFG => { let b_named = Named{ name: crate_.name, val: b};
                              build_cfg(analysis, b_named) }
                BuildDataflowContext => build_dfc(analysis, crate_),
                BuildRegionInferenceGraph => build_rig(analysis, crate_),
                GatherLoans => build_loans(analysis, crate_),
            }
        }
        _ => fail!("quoted input for cfg test must \
                              be a expression block { ... }")
    }
}

fn build_cfg(analysis: driver::CrateAnalysis, b: Named<ast::P<ast::Block>>) {
            let method_map = analysis.maps.method_map;
            let cfg = rustc_cfg::CFG::new(&analysis.ty_cx, method_map, b.val);
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

fn build_dfc(analysis: driver::CrateAnalysis, crate_: Named<ast::Crate>) {
    use rustc::middle::moves;
    use rustc::middle::borrowck;

    let moves::MoveMaps {moves_map, moved_variables_set, capture_map} =
        moves::compute_moves(&analysis.ty_cx, analysis.maps.method_map, &crate_.val);

    let mut b_ctxt = borrowck::BorrowckCtxt {
        tcx: &analysis.ty_cx,
        method_map: analysis.maps.method_map,
        moves_map: &moves_map,
        moved_variables_set: &moved_variables_set,
        capture_map: &capture_map,
        root_map: borrowck::root_map(),
        stats: @borrowck::BorrowStats {
            loaned_paths_same: cell::Cell::new(0),
            loaned_paths_imm:  cell::Cell::new(0),
            stable_paths:      cell::Cell::new(0),
            guaranteed_paths:  cell::Cell::new(0),
        },
    };

    let b = crate_.map(crate_to_decl_block);
    let (ident, purity, decl, abi, generics, body) = b.val;

    let (id_range, all_loans, _move_data) =
        borrowck::gather_loans::gather_loans_in_fn(&mut b_ctxt, decl, body);
    let loan_bitcount = cmp::max(1, all_loans.len());

    #[deriving(Clone)]
    struct Op;
    impl rustc_dataflow::DataFlowOperator for Op {
        fn initial_value(&self) -> bool { false }
        fn join(&self, succ: uint, pred: uint) -> uint { succ | pred }
    }
    #[cfg(localize_everything)]
    impl my_dataflow::DataFlowOperator for Op {
        fn initial_value(&self) -> bool { false }
        fn join(&self, succ: uint, pred: uint) -> uint { succ | pred }
    }

    let mut my_dfcx = my_dataflow::DataFlowContext::new(
        &analysis.ty_cx, analysis.maps.method_map, Op, id_range, loan_bitcount);
    let mut rs_dfcx = rustc_dataflow::DataFlowContext::new(
        &analysis.ty_cx, analysis.maps.method_map, Op, id_range, loan_bitcount);

    for (loan_idx, loan) in all_loans.iter().enumerate() {
        my_dfcx.add_gen(loan.gen_scope, loan_idx);
        rs_dfcx.add_gen(loan.gen_scope, loan_idx);
        my_dfcx.add_kill(loan.kill_scope, loan_idx);
        rs_dfcx.add_kill(loan.kill_scope, loan_idx);
    }

    my_dfcx.propagate(body);
    rs_dfcx.propagate(body);

    if loan_bitcount > 0 {
        dataflow_assert_matches(body, &mut my_dfcx, &mut rs_dfcx);
    }
}

fn build_rig(analysis: driver::CrateAnalysis, crate_: Named<ast::Crate>) {
    use rri = rustc::middle::typeck::infer::region_inference;
    fail!("not implemented yet");
}

fn dataflow_assert_matches<'a, O:MyOp+RsOp>(
    b: &ast::Block,
    my_dfcx: &'a mut MyDataflowCtxt<'a, O>,
    rs_dfcx: &'a mut RsDataflowCtxt<'a, O>)
{
    let mut visit = IdVisitor { my_dfcx: my_dfcx, rs_dfcx: rs_dfcx };
    visit.visit_block(b, ());

    struct IdVisitor<'a, O> {
        my_dfcx: &'a mut MyDataflowCtxt<'a, O>,
        rs_dfcx: &'a mut RsDataflowCtxt<'a, O>,
    }
    impl<'a, O:MyOp+RsOp> Visitor<()> for IdVisitor<'a, O> {
        fn visit_block(&mut self, b: &ast::Block, _: ()) {
            self.on_id(b.id);
            visit::walk_block(self, b, ());
        }
        fn visit_pat(&mut self, p: &ast::Pat, _: ()) {
            self.on_id(p.id);
            visit::walk_pat(self, p, ());
        }
        fn visit_expr(&mut self, ex: &ast::Expr, _: ()) {
            self.on_id(ex.id);
            visit::walk_expr(self, ex, ());
        }
    }
    impl<'a, O:MyOp+RsOp> IdVisitor<'a, O> {
        fn on_id(&mut self, id: ast::NodeId) {
            assert!(matches_at(self.my_dfcx, self.rs_dfcx, id));
        }
    }
}

fn build_loans(analysis: driver::CrateAnalysis, crate_: Named<ast::Crate>) {
    use rustc::middle::moves;
    use rs_borrowck = rustc::middle::borrowck;

    let moves::MoveMaps {moves_map, moved_variables_set, capture_map} =
        moves::compute_moves(&analysis.ty_cx, analysis.maps.method_map, &crate_.val);

    let mut rs_b_ctxt = rs_borrowck::BorrowckCtxt {
        tcx: &analysis.ty_cx,
        method_map: analysis.maps.method_map,
        moves_map: &moves_map,
        moved_variables_set: &moved_variables_set,
        capture_map: &capture_map,
        root_map: rs_borrowck::root_map(),
        stats: @rs_borrowck::BorrowStats {
            loaned_paths_same: cell::Cell::new(0),
            loaned_paths_imm:  cell::Cell::new(0),
            stable_paths:      cell::Cell::new(0),
            guaranteed_paths:  cell::Cell::new(0),
        },
    };

    let mut my_b_ctxt = my_borrowck::BorrowckCtxt {
        tcx: &analysis.ty_cx,
        method_map: analysis.maps.method_map,
        moves_map: &moves_map,
        moved_variables_set: &moved_variables_set,
        capture_map: &capture_map,
        root_map: my_borrowck::root_map(),
        stats: @my_borrowck::BorrowStats {
            loaned_paths_same: cell::Cell::new(0),
            loaned_paths_imm:  cell::Cell::new(0),
            stable_paths:      cell::Cell::new(0),
            guaranteed_paths:  cell::Cell::new(0),
        },
    };

    let b = crate_.clone().map(crate_to_decl_block);
    let (ident, purity, decl, abi, generics, body) = b.val;

    let mut rs_loan_dfcx = {
        let (id_range, all_loans, move_data) =
            rs_borrowck::gather_loans::gather_loans_in_fn(&mut rs_b_ctxt, decl, body);

        let mut loan_dfcx =
            rustc_dataflow::DataFlowContext::new(rs_b_ctxt.tcx,
                                                 rs_b_ctxt.method_map,
                                                 rs_borrowck::LoanDataFlowOperator,
                                                 id_range,
                                                 all_loans.len());
        for (loan_idx, loan) in all_loans.iter().enumerate() {
            loan_dfcx.add_gen(loan.gen_scope, loan_idx);
            loan_dfcx.add_kill(loan.kill_scope, loan_idx);
        }
        loan_dfcx.propagate(body);

        let flowed_moves = rs_borrowck::move_data::FlowedMoveData::new(move_data,
                                                                       rs_b_ctxt.tcx,
                                                                       rs_b_ctxt.method_map,
                                                                       id_range,
                                                                       body);

        rs_borrowck::check_loans::check_loans(&rs_b_ctxt, &loan_dfcx, flowed_moves,
                                              all_loans.as_slice(), body);

        let fk = visit::FkItemFn(ident, &generics, purity, abi::AbiSet::Rust());
        visit::walk_fn(&mut rs_b_ctxt,
                       &fk,
                       decl,
                       body,
                       codemap::DUMMY_SP,
                       ast::DUMMY_NODE_ID,
                       ());

        loan_dfcx
    };

    let mut my_loan_dfcx = {
        let (id_range, all_loans, move_data) =
            my_borrowck::gather_loans::gather_loans_in_fn(&mut my_b_ctxt, decl, body);

        let mut loan_dfcx =
            rustc_dataflow::DataFlowContext::new(my_b_ctxt.tcx,
                                                 my_b_ctxt.method_map,
                                                 my_borrowck::LoanDataFlowOperator,
                                                 id_range,
                                                 all_loans.len());
        for (loan_idx, loan) in all_loans.iter().enumerate() {
            loan_dfcx.add_gen(loan.gen_scope, loan_idx);
            loan_dfcx.add_kill(loan.kill_scope, loan_idx);
        }
        loan_dfcx.propagate(body);

        let flowed_moves = my_borrowck::move_data::FlowedMoveData::new(move_data,
                                                                       my_b_ctxt.tcx,
                                                                       my_b_ctxt.method_map,
                                                                       id_range,
                                                                       body);

        my_borrowck::check_loans::check_loans(&my_b_ctxt, &loan_dfcx, flowed_moves,
                                              all_loans.as_slice(), body);

        let fk = visit::FkItemFn(ident, &generics, purity, abi::AbiSet::Rust());
        visit::walk_fn(&mut my_b_ctxt,
                       &fk,
                       decl,
                       body,
                       codemap::DUMMY_SP,
                       ast::DUMMY_NODE_ID,
                       ());

        loan_dfcx
    };

    loans_assert_matches(body, &mut my_loan_dfcx, &mut rs_loan_dfcx);
}

fn loans_assert_matches<'a,
                        MyO:RsOp,
                        RsO:RsOp,
                        MyC: AbstractDataFlowContext<MyO>,
                        RsC: AbstractDataFlowContext<RsO>>(
    b: &ast::Block, my_dfcx: &'a mut MyC, rs_dfcx: &'a mut RsC)
{
    let mut visit = IdVisitor { my_dfcx: my_dfcx, rs_dfcx: rs_dfcx };
    visit.visit_block(b, ());

    struct IdVisitor<'a, MyC /*: AbstractDataFlowContext*/, RsC /*: AbstractDataFlowContext*/> {
        my_dfcx: &'a mut MyC,
        rs_dfcx: &'a mut RsC,
    }
    impl<'a,
         MyO:MyOp,
         RsO:RsOp,
         MyC:AbstractDataFlowContext<MyO>,
         RsC:AbstractDataFlowContext<RsO>>
        Visitor<()>
        for IdVisitor<'a, MyC, RsC> {
        fn visit_block(&mut self, b: &ast::Block, _: ()) {
            self.on_id(b.id);
            visit::walk_block(self, b, ());
        }
        fn visit_pat(&mut self, p: &ast::Pat, _: ()) {
            self.on_id(p.id);
            visit::walk_pat(self, p, ());
        }
        fn visit_expr(&mut self, ex: &ast::Expr, _: ()) {
            self.on_id(ex.id);
            visit::walk_expr(self, ex, ());
        }
    }
    impl<'a,
         MyO:MyOp,
         RsO:RsOp,
         MyC:AbstractDataFlowContext<MyO>,
         RsC:AbstractDataFlowContext<RsO>>
        IdVisitor<'a, MyC, RsC> {
        fn on_id(&mut self, id: ast::NodeId) {
            assert!(matches_at(self.my_dfcx, self.rs_dfcx, id));
        }
    }
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
