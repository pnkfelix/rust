// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrowck::BorrowckCtxt;

use syntax::ast::{self, NodeId};
use syntax::codemap::Span;

use rustc_front::hir;
use rustc_front::intravisit::{FnKind};

use rustc::mir::repr::{BasicBlock, BasicBlockData, Mir, Statement, Terminator};
use rustc::session::Session;

mod abs_domain;
mod dataflow;
mod gather_moves;
mod graphviz;

pub use self::dataflow::{BitDenotation};
use self::dataflow::{Dataflow, DataflowState, DataflowStateBuilder};
use self::dataflow::{MaybeInitializedLvals, MaybeUninitializedLvals};
use self::gather_moves::{MoveData};

pub use self::gather_moves::{MovePathContent};

use std::fmt::Debug;

#[derive(Debug)]
pub struct BorrowckMirData<'tcx> {
    pub move_data: MoveData<'tcx>,
    pub flow_inits: DataflowState<MaybeInitializedLvals<'tcx>>,
    pub flow_uninits: DataflowState<MaybeUninitializedLvals<'tcx>>,
}

pub fn borrowck_mir<'b, 'a: 'b, 'tcx: 'a>(
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    fk: FnKind,
    _decl: &hir::FnDecl,
    mir: &'a Mir<'tcx>,
    body: &hir::Block,
    _sp: Span,
    id: ast::NodeId,
    attributes: &[ast::Attribute]) -> BorrowckMirData<'tcx> {
    match fk {
        FnKind::ItemFn(name, _, _, _, _, _, _) |
        FnKind::Method(name, _, _, _) => {
            debug!("borrowck_mir({}) UNIMPLEMENTED", name);
        }
        FnKind::Closure(_) => {
            debug!("borrowck_mir closure (body.id={}) UNIMPLEMENTED", body.id);
        }
    }

    let move_data = MoveData::gather_moves(mir, bcx.tcx);

    let (move_data, flow_inits) =
        do_dataflow(bcx, mir, id, attributes, move_data, MaybeInitializedLvals::default());
    let (move_data, flow_uninits) =
        do_dataflow(bcx, mir, id, attributes, move_data, MaybeUninitializedLvals::default());

    let mut mbcx = MirBorrowckCtxt {
        bcx: bcx,
        mir: mir,
        node_id: id,
        move_data: move_data,
        flow_inits: flow_inits,
        flow_uninits: flow_uninits,
    };

    for bb in mir.all_basic_blocks() {
        mbcx.process_basic_block(bb);
    }

    debug!("borrowck_mir done");

    return BorrowckMirData {
        move_data: mbcx.move_data,
        flow_inits: mbcx.flow_inits,
        flow_uninits: mbcx.flow_uninits,
    };

    fn do_dataflow<'a, 'tcx, BD>(bcx: &mut BorrowckCtxt<'a, 'tcx>,
                                 mir: &'a Mir<'tcx>,
                                 node_id: NodeId,
                                 attributes: &[ast::Attribute],
                                 move_data: MoveData<'tcx>,
                                 bd: BD) -> (MoveData<'tcx>, DataflowState<BD>)
        where BD: BitDenotation<Ctxt=MoveData<'tcx>>, BD::Bit: Debug
    {
        use syntax::attr::AttrMetaMethods;

        let attr_meta_name_found = |sess: &Session, attributes: &[ast::Attribute], name| -> Option<String> {
            for attr in attributes {
                if attr.check_name("rustc_mir") {
                    let items = attr.meta_item_list();
                    for item in items.iter().flat_map(|l| l.iter()) {
                        if item.check_name(name) {
                            if let Some(s) = item.value_str() {
                                return Some(s.to_string())
                            } else {
                                sess.span_err(
                                    item.span,
                                    &format!("{} attribute requires a path", item.name()));
                                return None;
                            }
                        }
                    }
                }
            }
            return None;
        };

        let print_preflow_to =
            attr_meta_name_found(bcx.tcx.sess, attributes, "borrowck_graphviz_preflow");
        let print_postflow_to =
            attr_meta_name_found(bcx.tcx.sess, attributes, "borrowck_graphviz_postflow");

        let mut mbcx = MirBorrowckCtxtPreDataflow {
            bcx: bcx,
            mir: mir,
            node_id: node_id,
            print_preflow_to: print_preflow_to,
            print_postflow_to: print_postflow_to,
            flow_state: DataflowStateBuilder::new(mir, move_data, bd),
        };

        mbcx.dataflow();
        mbcx.flow_state.unpack()
    }
}

pub struct MirBorrowckCtxtPreDataflow<'b, 'a: 'b, 'tcx: 'a, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>
{
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    mir: &'b Mir<'tcx>,
    node_id: ast::NodeId,
    print_preflow_to: Option<String>,
    print_postflow_to: Option<String>,
    flow_state: DataflowStateBuilder<'a, 'tcx, BD>,
}

pub struct MirBorrowckCtxt<'b, 'a: 'b, 'tcx: 'a> {
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    mir: &'b Mir<'tcx>,
    node_id: ast::NodeId,
    move_data: MoveData<'tcx>,
    flow_inits: DataflowState<MaybeInitializedLvals<'tcx>>,
    flow_uninits: DataflowState<MaybeUninitializedLvals<'tcx>>,
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn process_basic_block(&mut self, bb: BasicBlock) {
        let &BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
            self.mir.basic_block_data(bb);
        for stmt in statements {
            self.process_statement(bb, stmt);
        }

        self.process_terminator(bb, terminator);
    }

    fn process_statement(&mut self, bb: BasicBlock, stmt: &Statement<'tcx>) {
        debug!("MirBorrowckCtxt::process_statement({:?}, {:?}", bb, stmt);
    }

    fn process_terminator(&mut self, bb: BasicBlock, term: &Option<Terminator<'tcx>>) {
        debug!("MirBorrowckCtxt::process_terminator({:?}, {:?})", bb, term);
    }
}
