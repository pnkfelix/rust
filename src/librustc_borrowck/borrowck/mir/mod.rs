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

use syntax::ast;
use syntax::codemap::Span;

use rustc_front::hir;
use rustc_front::intravisit::{FnKind};

use rustc::mir::repr::{BasicBlock, BasicBlockData, Mir, Statement, Terminator};

mod abs_domain;
mod dataflow;
mod gather_moves;
mod graphviz;

use self::dataflow::{BitDenotation};
use self::dataflow::{Dataflow, DataflowState, DataflowStateBuilder};
use self::dataflow::{MovingOutStatements};
use self::gather_moves::{MoveData};

pub fn borrowck_mir<'b, 'a: 'b, 'tcx: 'a>(
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    fk: FnKind,
    _decl: &hir::FnDecl,
    mir: &'a Mir<'tcx>,
    body: &hir::Block,
    _sp: Span,
    id: ast::NodeId,
    attributes: &[ast::Attribute]) {
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

    let (moving_statements_flow, move_data) = {
        let mut mbcx = MirBorrowckCtxtPreDataflow {
            bcx: bcx,
            mir: mir,
            node_id: id,
            attributes: attributes,
            flow_state: DataflowStateBuilder::new(mir, move_data, MovingOutStatements::default()),
        };

        mbcx.dataflow();
        mbcx.flow_state.unpack()
    };

    let mut mbcx = MirBorrowckCtxt {
        bcx: bcx,
        mir: mir,
        node_id: id,
        attributes: attributes,
        move_data: move_data,
        flow_state: moving_statements_flow,
    };

    for bb in mir.all_basic_blocks() {
        mbcx.process_basic_block(bb);
    }

    debug!("borrowck_mir done");
}

pub struct MirBorrowckCtxtPreDataflow<'b, 'a: 'b, 'tcx: 'a, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>
{
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    mir: &'b Mir<'tcx>,
    node_id: ast::NodeId,
    attributes: &'b [ast::Attribute],
    flow_state: DataflowStateBuilder<'a, 'tcx, BD>,
}

pub struct MirBorrowckCtxt<'b, 'a: 'b, 'tcx: 'a> {
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    mir: &'b Mir<'tcx>,
    node_id: ast::NodeId,
    attributes: &'b [ast::Attribute],
    move_data: MoveData<'tcx>,
    flow_state: DataflowState<MovingOutStatements<'tcx>>,
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
