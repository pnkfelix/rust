// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{MirBorrowckCtxt, each_bit};

use super::dataflow::{BitDenotation, BlockSets};
use super::dataflow::{DataflowResults, DataflowResultsConsumer};
use super::dataflow::{Borrows, BorrowData, MovingOutStatements};
use super::dataflow::{MaybeInitializedLvals, MaybeUninitializedLvals};
use super::gather_moves::{HasMoveData, BorrowIndex};

use self::MutateMode::{JustWrite, WriteAndRead};

use rustc::mir::{AssertMessage, BasicBlock, BorrowKind, Mir, Location};
use rustc::mir::{Lvalue, Rvalue, Operand};
use rustc::mir::{Statement, StatementKind, Terminator, TerminatorKind};

use rustc_data_structures::indexed_set::{IdxSetBuf};
use rustc_data_structures::indexed_vec::{Idx};
use syntax_pos::DUMMY_SP;

struct FlowInProgress<BD> where BD: BitDenotation {
    base_results: DataflowResults<BD>,
    curr_state: IdxSetBuf<BD::Idx>,
    stmt_gen: IdxSetBuf<BD::Idx>,
    stmt_kill: IdxSetBuf<BD::Idx>,
}

impl<BD> FlowInProgress<BD> where BD: BitDenotation {
    fn each_state_bit<F>(&self, f: F) where F: FnMut(BD::Idx) {
        each_bit(&self.curr_state, self.base_results.operator().bits_per_block(), f)
    }

    fn each_gen_bit<F>(&self, f: F) where F: FnMut(BD::Idx) {
        each_bit(&self.stmt_gen, self.base_results.operator().bits_per_block(), f)
    }
}

impl<BD> FlowInProgress<BD> where BD: BitDenotation {
    fn new(results: DataflowResults<BD>) -> Self {
        let bits_per_block = results.sets().bits_per_block();
        let curr_state = IdxSetBuf::new_empty(bits_per_block);
        let stmt_gen = IdxSetBuf::new_empty(bits_per_block);
        let stmt_kill = IdxSetBuf::new_empty(bits_per_block);
        FlowInProgress {
            base_results: results,
            curr_state: curr_state,
            stmt_gen: stmt_gen,
            stmt_kill: stmt_kill,
        }
    }

    fn reset_to_entry_of(&mut self, bb: BasicBlock) {
        (*self.curr_state).clone_from(self.base_results.sets().on_entry_set_for(bb.index()));
    }

    fn reconstruct_statement_effect(&mut self, loc: Location) {
        self.stmt_gen.reset_to_empty();
        self.stmt_kill.reset_to_empty();
        let mut ignored = IdxSetBuf::new_empty(0);
        let mut sets = BlockSets {
            on_entry: &mut ignored, gen_set: &mut self.stmt_gen, kill_set: &mut self.stmt_kill,
        };
        self.base_results.operator().statement_effect(&mut sets, loc);
    }

    fn reconstruct_terminator_effect(&mut self, loc: Location) {
        self.stmt_gen.reset_to_empty();
        self.stmt_kill.reset_to_empty();
        let mut ignored = IdxSetBuf::new_empty(0);
        let mut sets = BlockSets {
            on_entry: &mut ignored, gen_set: &mut self.stmt_gen, kill_set: &mut self.stmt_kill,
        };
        self.base_results.operator().terminator_effect(&mut sets, loc);
    }

    fn apply_local_effect(&mut self) {
        self.curr_state.union(&self.stmt_gen);
        self.curr_state.subtract(&self.stmt_kill);
    }
}

// (forced to be `pub` due to its use as an associated type below.)
pub struct InProgress<'b, 'tcx: 'b> {
    borrows: FlowInProgress<Borrows<'b, 'tcx>>,
    inits: FlowInProgress<MaybeInitializedLvals<'b, 'tcx>>,
    uninits: FlowInProgress<MaybeUninitializedLvals<'b, 'tcx>>,
    move_outs: FlowInProgress<MovingOutStatements<'b, 'tcx>>,
}

impl<'b, 'tcx: 'b> InProgress<'b, 'tcx> {
    pub(super) fn new(borrows: DataflowResults<Borrows<'b, 'tcx>>,
                      inits: DataflowResults<MaybeInitializedLvals<'b, 'tcx>>,
                      uninits: DataflowResults<MaybeUninitializedLvals<'b, 'tcx>>,
                      move_outs: DataflowResults<MovingOutStatements<'b, 'tcx>>) -> Self {
        InProgress {
            borrows: FlowInProgress::new(borrows),
            inits: FlowInProgress::new(inits),
            uninits: FlowInProgress::new(uninits),
            move_outs: FlowInProgress::new(move_outs),
        }
    }

    fn each_flow<XB, XI, XU>(&mut self,
                             mut xform_borrows: XB,
                             mut xform_inits: XI,
                             mut xform_uninits: XU) where
        XB: FnMut(&mut FlowInProgress<Borrows<'b, 'tcx>>),
        XI: FnMut(&mut FlowInProgress<MaybeInitializedLvals<'b, 'tcx>>),
        XU: FnMut(&mut FlowInProgress<MaybeUninitializedLvals<'b, 'tcx>>),
    {
        xform_borrows(&mut self.borrows);
        xform_inits(&mut self.inits);
        xform_uninits(&mut self.uninits);
    }

    fn summary(&self) -> String {
        let mut s = String::new();

        s.push_str("borrows in effect: [");
        let mut saw_one = false;
        self.borrows.each_state_bit(|borrow| {
            if saw_one { s.push_str(", "); };
            saw_one = true;
            let borrow_data = &self.borrows.base_results.operator().borrows()[borrow];
            s.push_str(&format!("{}", borrow_data));
        });
        s.push_str("] ");

        s.push_str("borrows generated: [");
        let mut saw_one = false;
        self.borrows.each_gen_bit(|borrow| {
            if saw_one { s.push_str(", "); };
            saw_one = true;
            let borrow_data = &self.borrows.base_results.operator().borrows()[borrow];
            s.push_str(&format!("{}", borrow_data));
        });
        s.push_str("] ");

        s.push_str("inits: [");
        let mut saw_one = false;
        self.inits.each_state_bit(|mpi_init| {
            if saw_one { s.push_str(", "); };
            saw_one = true;
            let move_path =
                &self.inits.base_results.operator().move_data().move_paths[mpi_init];
            s.push_str(&format!("{}", move_path));
        });
        s.push_str("] ");

        s.push_str("uninits: [");
        let mut saw_one = false;
        self.uninits.each_state_bit(|mpi_uninit| {
            if saw_one { s.push_str(", "); };
            saw_one = true;
            let move_path =
                &self.uninits.base_results.operator().move_data().move_paths[mpi_uninit];
            s.push_str(&format!("{}", move_path));
        });
        s.push_str("]");

        return s;
    }
}

// Check that:
// 1. assignments are always made to mutable locations (FIXME: does that still really go here?)
// 2. loans made in overlapping scopes do not conflict
// 3. assignments do not affect things loaned out as immutable
// 4. moves do not affect things loaned out in any way
impl<'b, 'a: 'b, 'tcx: 'a> DataflowResultsConsumer<'b, 'tcx> for MirBorrowckCtxt<'b, 'a, 'tcx> {
    type FlowState = InProgress<'b, 'tcx>;

    fn mir(&self) -> &'b Mir<'tcx> { self.mir }

    fn reset_to_entry_of(&mut self, bb: BasicBlock, flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.reset_to_entry_of(bb),
                             |i| i.reset_to_entry_of(bb),
                             |u| u.reset_to_entry_of(bb));
    }

    fn reconstruct_statement_effect(&mut self,
                                    location: Location,
                                    flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.reconstruct_statement_effect(location),
                             |i| i.reconstruct_statement_effect(location),
                             |u| u.reconstruct_statement_effect(location));
    }

    fn apply_local_effect(&mut self,
                          _location: Location,
                          flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.apply_local_effect(),
                             |i| i.apply_local_effect(),
                             |u| u.apply_local_effect());
    }

    fn reconstruct_terminator_effect(&mut self,
                                     location: Location,
                                    flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.reconstruct_terminator_effect(location),
                             |i| i.reconstruct_terminator_effect(location),
                             |u| u.reconstruct_terminator_effect(location));
    }

    fn visit_block_entry(&mut self,
                         bb: BasicBlock,
                         flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_block({:?}): {}", bb, summary);
    }

    fn visit_statement_entry(&mut self,
                             location: Location,
                             stmt: &Statement<'tcx>,
                             flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_statement({:?}, {:?}): {}", location, stmt, summary);
        match stmt.kind {
            StatementKind::Assign(ref lhs, ref rhs) => {
                self.mutate_lvalue(lhs, JustWrite, flow_state);
                self.consume_rvalue(rhs, location, flow_state);
            }
            StatementKind::SetDiscriminant { ref lvalue, variant_index: _ } => {
                // FIXME: should this count as a mutate from borrowck POV?
                self.mutate_lvalue(lvalue, JustWrite, flow_state);
            }
            StatementKind::InlineAsm { ref asm, ref outputs, ref inputs } => {
                for (o, output) in asm.outputs.iter().zip(outputs) {
                    if o.is_indirect {
                        self.consume_lvalue(output, flow_state);
                    } else {
                        self.mutate_lvalue(output, if o.is_rw { WriteAndRead } else { JustWrite }, flow_state);
                    }
                }
                for input in inputs {
                    self.consume_operand(input, flow_state);
                }
            }
            StatementKind::EndRegion(ref _rgn) => {
                // ignored when consuming results (update to
                // flow_state already handled).
            }
            StatementKind::Nop |
            StatementKind::StorageLive(..) |
            StatementKind::StorageDead(..) => {
                // ignored by borrowck
            }
        }
    }

    fn visit_terminator_entry(&mut self,
                              location: Location,
                              term: &Terminator<'tcx>,
                              flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_terminator({:?}, {:?}): {}", location, term, summary);
        match term.kind {
            TerminatorKind::SwitchInt { ref discr, switch_ty: _, values: _, targets: _ } => {
                self.consume_operand(discr, flow_state);
            }
            TerminatorKind::Drop { ref location, target: _, unwind: _ } => {
                self.consume_lvalue(location, flow_state);
            }
            TerminatorKind::DropAndReplace { ref location, ref value, target: _, unwind: _ } => {
                self.mutate_lvalue(location, JustWrite, flow_state);
                self.consume_operand(value, flow_state);
            }
            TerminatorKind::Call { ref func, ref args, ref destination, cleanup: _ } => {
                self.consume_operand(func, flow_state);
                for arg in args { self.consume_operand(arg, flow_state); }
                if let Some((ref dest, _/*bb*/)) = *destination {
                    self.mutate_lvalue(dest, JustWrite, flow_state);
                }
            }
            TerminatorKind::Assert { ref cond, expected: _, ref msg, target: _, cleanup: _ } => {
                self.consume_operand(cond, flow_state);
                match *msg {
                    AssertMessage::BoundsCheck { ref len, ref index } => {
                        self.consume_operand(len, flow_state);
                        self.consume_operand(index, flow_state);
                    }
                    AssertMessage::Math(_/*const_math_err*/) => {}
                }
            }

            TerminatorKind::Goto { target: _ } |
            TerminatorKind::Resume |
            TerminatorKind::Return |
            TerminatorKind::Unreachable => {
                // no data used, thus irrelevant to borrowck
            }
        }
    }
}

enum MutateMode { JustWrite, WriteAndRead }

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn mutate_lvalue(&mut self,
                     lvalue: &Lvalue<'tcx>,
                     mode: MutateMode,
                     flow_state: &InProgress<'b, 'tcx>) {
        // Write of P[i] or *P, or WriteAndRead of any P, requires P init'd.
        match mode {
            MutateMode::WriteAndRead => {
                self.check_if_path_is_moved(lvalue, flow_state);
            }
            MutateMode::JustWrite => {
                self.check_if_assigned_path_is_moved(lvalue, flow_state);
            }
        }

        // check we don't invalidate any outstanding loans
        if true { unimplemented!(); }

        // check for reassignments to immutable local variables
        if true { unimplemented!(); }
    }

    fn consume_rvalue(&mut self,
                      rvalue: &Rvalue<'tcx>,
                      _location: Location,
                      flow_state: &InProgress<'b, 'tcx>) {
        match *rvalue {
            Rvalue::Ref(_/*rgn*/, BorrowKind::Shared, ref lvalue) => {
                self.borrow_shared(lvalue, flow_state)
            }

            Rvalue::Ref(_/*rgn*/, BorrowKind::Mut, ref lvalue) |
            Rvalue::Ref(_/*rgn*/, BorrowKind::Unique, ref lvalue) => {
                self.borrow_mut(lvalue, flow_state)
            }

            Rvalue::Use(ref operand) |
            Rvalue::Repeat(ref operand, _) |
            Rvalue::UnaryOp(_/*un_op*/, ref operand) |
            Rvalue::Cast(_/*cast_kind*/, ref operand, _/*ty*/) => {
                self.consume_operand(operand, flow_state)
            }

            Rvalue::Len(ref lvalue) |
            Rvalue::Discriminant(ref lvalue) => {
                self.consume_lvalue(lvalue, flow_state)
            }

            Rvalue::BinaryOp(_bin_op, ref operand1, ref operand2) |
            Rvalue::CheckedBinaryOp(_bin_op, ref operand1, ref operand2) => {
                self.consume_operand(operand1, flow_state);
                self.consume_operand(operand2, flow_state);
            }

            Rvalue::Box(_ty) => {
                // creates an uninitialized box; no borrowck effect.
            }

            Rvalue::Aggregate(ref _aggregate_kind, ref operands) => {
                for operand in operands {
                    self.consume_operand(operand, flow_state);
                }
            }
        }
    }

    fn consume_operand(&mut self,
                       operand: &Operand<'tcx>,
                       flow_state: &InProgress<'b, 'tcx>) {
        match *operand {
            Operand::Consume(ref lvalue) => self.consume_lvalue(lvalue, flow_state),
            Operand::Constant(_) => {}
        }
    }

    fn consume_lvalue(&mut self,
                      lvalue: &Lvalue<'tcx>,
                      flow_state: &InProgress<'b, 'tcx>) {
        let ty = lvalue.ty(self.mir, self.bcx.tcx).to_ty(self.bcx.tcx);
        let moves_by_default = self.fake_infer_ctxt.type_moves_by_default(ty, DUMMY_SP);
        if moves_by_default {
            // move of lvalue: check if this is move of borrowed path
            flow_state.each_borrow_involving_path(lvalue, |_idx, borrow| {
                if !borrow.compatible_with_mut_borrow() { self.report_use_while_borrowed(); }
            });
        } else {
            // copy of lvalue: check if this is "copy of frozen path" (FIXME: see check_loans.rs)
            flow_state.each_borrow_involving_path(lvalue, |_idx, borrow| {
                if !borrow.compatible_with_imm_borrow() { self.report_use_while_borrowed(); }
            });
        }

        // Finally, check if path was already moved.
        self.check_if_path_is_moved(lvalue, flow_state);
    }

    fn borrow_shared(&mut self, lvalue: &Lvalue<'tcx>, flow_state: &InProgress<'b, 'tcx>) {
        self.check_if_path_is_moved(lvalue, flow_state);
        self.check_for_conflicting_loan(lvalue, flow_state);
    }

    fn borrow_mut(&mut self, _lvalue: &Lvalue<'tcx>, _flow_state: &InProgress<'b, 'tcx>) {
        unimplemented!()
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn check_if_path_is_moved(&mut self,
                              _lvalue: &Lvalue<'tcx>,
                              flow_state: &InProgress<'b, 'tcx>) {
        // for each move in flow_state.move_outs ...
        &flow_state.move_outs;
        unimplemented!()
    }

    fn check_if_assigned_path_is_moved(&mut self,
                                       _lvalue: &Lvalue<'tcx>,
                                       _flow_state: &InProgress<'b, 'tcx>) {
        // recur over lvalue to find if any cases need to to dispatch to check_if_path_is_moved
        unimplemented!()
    }

    fn check_for_conflicting_loan(&mut self,
                                  _lvalue: &Lvalue<'tcx>,
                                  _flow_state: &InProgress<'b, 'tcx>) {
        // for each borrow in flow_state, ...
        unimplemented!()
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn report_use_while_borrowed(&mut self) {
        unimplemented!()
    }
}

impl<'tcx> BorrowData<'tcx> {
    fn compatible_with_mut_borrow(&self) -> bool { unimplemented!() }

    fn compatible_with_imm_borrow(&self) -> bool { unimplemented!() }
}

impl<'b, 'tcx> InProgress<'b, 'tcx> {
    fn each_borrow_involving_path<F>(&self, _lvalue: &Lvalue, _op: F)
        where F: FnMut(BorrowIndex, &BorrowData)
    {
        unimplemented!()
    }
}
