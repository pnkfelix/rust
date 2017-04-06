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
use super::gather_moves::{HasMoveData, BorrowIndex, LookupResult};
use super::gather_moves::{MoveData, MovePathIndex};

use self::MutateMode::{JustWrite, WriteAndRead};

use rustc::hir;
use rustc::mir::{AssertMessage, BasicBlock, BorrowKind, Mir, Location};
use rustc::mir::{Lvalue, Rvalue, Mutability, Operand, Projection, ProjectionElem};
use rustc::mir::{Statement, StatementKind, Terminator, TerminatorKind};
use rustc::ty::{self, TyCtxt};

use rustc_data_structures::indexed_set::{self, IdxSetBuf};
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

impl<BD: BitDenotation> FlowInProgress<BD> {
    fn elems_generated(&self) -> indexed_set::Elems<BD::Idx> {
        let univ = self.base_results.sets().bits_per_block();
        self.stmt_gen.elems(univ)
    }

    fn pairs_generated(&self) -> indexed_set::Pairs<BD::Idx> {
        let univ = self.base_results.sets().bits_per_block();
        self.stmt_gen.pairs(univ)
    }

    fn elems_incoming(&self) -> indexed_set::Elems<BD::Idx> {
        let univ = self.base_results.sets().bits_per_block();
        self.curr_state.elems(univ)
    }
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
                self.mutate_lvalue(ContextKind::AssignLhs.new(location),
                                   lhs, JustWrite, flow_state);
                self.consume_rvalue(ContextKind::AssignRhs.new(location),
                                    rhs, location, flow_state);
            }
            StatementKind::SetDiscriminant { ref lvalue, variant_index: _ } => {
                // FIXME: should this count as a mutate from borrowck POV?
                self.mutate_lvalue(ContextKind::SetDiscrim.new(location),
                                   lvalue, JustWrite, flow_state);
            }
            StatementKind::InlineAsm { ref asm, ref outputs, ref inputs } => {
                for (o, output) in asm.outputs.iter().zip(outputs) {
                    if o.is_indirect {
                        self.consume_lvalue(ContextKind::InlineAsm.new(location),
                                            output,
                                            flow_state);
                    } else {
                        self.mutate_lvalue(ContextKind::InlineAsm.new(location),
                                           output,
                                           if o.is_rw { WriteAndRead } else { JustWrite },
                                           flow_state);
                    }
                }
                for input in inputs {
                    self.consume_operand(ContextKind::InlineAsm.new(location),
                                         input, flow_state);
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
        let loc = location;
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_terminator({:?}, {:?}): {}", location, term, summary);
        match term.kind {
            TerminatorKind::SwitchInt { ref discr, switch_ty: _, values: _, targets: _ } => {
                self.consume_operand(ContextKind::SwitchInt.new(loc),
                                     discr, flow_state);
            }
            TerminatorKind::Drop { ref location, target: _, unwind: _ } => {
                self.consume_lvalue(ContextKind::Drop.new(loc),
                                    location, flow_state);
            }
            TerminatorKind::DropAndReplace { ref location, ref value, target: _, unwind: _ } => {
                self.mutate_lvalue(ContextKind::DropAndReplace.new(loc),
                                   location, JustWrite, flow_state);
                self.consume_operand(ContextKind::DropAndReplace.new(loc),
                                     value, flow_state);
            }
            TerminatorKind::Call { ref func, ref args, ref destination, cleanup: _ } => {
                self.consume_operand(ContextKind::CallOperator.new(loc),
                                     func, flow_state);
                for arg in args {
                    self.consume_operand(ContextKind::CallOperand.new(loc),
                                         arg, flow_state);
                }
                if let Some((ref dest, _/*bb*/)) = *destination {
                    self.mutate_lvalue(ContextKind::CallDest.new(loc),
                                       dest, JustWrite, flow_state);
                }
            }
            TerminatorKind::Assert { ref cond, expected: _, ref msg, target: _, cleanup: _ } => {
                self.consume_operand(ContextKind::Assert.new(loc), cond, flow_state);
                match *msg {
                    AssertMessage::BoundsCheck { ref len, ref index } => {
                        self.consume_operand(ContextKind::Assert.new(loc), len, flow_state);
                        self.consume_operand(ContextKind::Assert.new(loc), index, flow_state);
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

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Context {
    kind: ContextKind,
    loc: Location,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum ContextKind {
    AssignLhs,
    AssignRhs,
    SetDiscrim,
    InlineAsm,
    SwitchInt,
    Drop,
    DropAndReplace,
    CallOperator,
    CallOperand,
    CallDest,
    Assert,
}

impl ContextKind {
    fn new(self, loc: Location) -> Context { Context { kind: self, loc: loc } }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum MutateMode { JustWrite, WriteAndRead }

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn mutate_lvalue(&mut self,
                     context: Context,
                     lvalue: &Lvalue<'tcx>,
                     mode: MutateMode,
                     flow_state: &InProgress<'b, 'tcx>) {
        // Write of P[i] or *P, or WriteAndRead of any P, requires P init'd.
        match mode {
            MutateMode::WriteAndRead => {
                self.check_if_path_is_moved(context, lvalue, flow_state);
            }
            MutateMode::JustWrite => {
                self.check_if_assigned_path_is_moved(context, lvalue, flow_state);
            }
        }

        // check we don't invalidate any outstanding loans
        self.each_borrow_involving_path(context,
                                        lvalue, flow_state, |this, _index, _data| {
                                            this.report_illegal_mutation(context);
                                        });

        // check for reassignments to immutable local variables
        self.check_if_reassignment_to_immutable_state(context, lvalue, flow_state);
    }

    fn consume_rvalue(&mut self,
                      context: Context,
                      rvalue: &Rvalue<'tcx>,
                      location: Location,
                      flow_state: &InProgress<'b, 'tcx>) {
        match *rvalue {
            Rvalue::Ref(_/*rgn*/, bk, ref lvalue) => {
                self.borrow(context, location, bk, lvalue, flow_state)
            }

            Rvalue::Use(ref operand) |
            Rvalue::Repeat(ref operand, _) |
            Rvalue::UnaryOp(_/*un_op*/, ref operand) |
            Rvalue::Cast(_/*cast_kind*/, ref operand, _/*ty*/) => {
                self.consume_operand(context, operand, flow_state)
            }

            Rvalue::Len(ref lvalue) |
            Rvalue::Discriminant(ref lvalue) => {
                self.consume_lvalue(context, lvalue, flow_state)
            }

            Rvalue::BinaryOp(_bin_op, ref operand1, ref operand2) |
            Rvalue::CheckedBinaryOp(_bin_op, ref operand1, ref operand2) => {
                self.consume_operand(context, operand1, flow_state);
                self.consume_operand(context, operand2, flow_state);
            }

            Rvalue::Box(_ty) => {
                // creates an uninitialized box; no borrowck effect.
            }

            Rvalue::Aggregate(ref _aggregate_kind, ref operands) => {
                for operand in operands {
                    self.consume_operand(context, operand, flow_state);
                }
            }
        }
    }

    fn consume_operand(&mut self,
                       context: Context,
                       operand: &Operand<'tcx>,
                       flow_state: &InProgress<'b, 'tcx>) {
        match *operand {
            Operand::Consume(ref lvalue) =>
                self.consume_lvalue(context, lvalue, flow_state),
            Operand::Constant(_) => {}
        }
    }

    fn consume_lvalue(&mut self,
                      context: Context,
                      lvalue: &Lvalue<'tcx>,
                      flow_state: &InProgress<'b, 'tcx>) {
        let ty = lvalue.ty(self.mir, self.bcx.tcx).to_ty(self.bcx.tcx);
        let moves_by_default = self.fake_infer_ctxt.type_moves_by_default(ty, DUMMY_SP);
        if moves_by_default {
            // move of lvalue: check if this is move of already borrowed path
            self.each_borrow_involving_path(context,
                                            lvalue, flow_state, |this, _idx, borrow| {
                if !borrow.compatible_with(BorrowKind::Mut) {
                    this.report_use_while_borrowed(context);
                }
            });
        } else {
            // copy of lvalue: check if this is "copy of frozen path" (FIXME: see check_loans.rs)
            self.each_borrow_involving_path(context,
                                            lvalue, flow_state, |this, _idx, borrow| {
                if !borrow.compatible_with(BorrowKind::Shared) {
                    this.report_use_while_borrowed(context);
                }
            });
        }

        // Finally, check if path was already moved.
        self.check_if_path_is_moved(context, lvalue, flow_state);
    }

    fn borrow(&mut self,
              context: Context,
              location: Location,
              bk: BorrowKind,
              lvalue: &Lvalue<'tcx>,
              flow_state: &InProgress<'b, 'tcx>) {
        self.check_if_path_is_moved(context, lvalue, flow_state);
        self.check_for_conflicting_loan(context, location, bk, lvalue, flow_state);
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn check_if_reassignment_to_immutable_state(&mut self,
                                                context: Context,
                                                lvalue: &Lvalue<'tcx>,
                                                flow_state: &InProgress<'b, 'tcx>) {
        let move_data = flow_state.inits.base_results.operator().move_data();

        // determine if this path has a non-mut owner (and thus needs checking).
        let mut l = lvalue;
        loop {
            match *l {
                Lvalue::Projection(ref proj) => {
                    l = &proj.base;
                    continue;
                }
                Lvalue::Local(local) => {
                    match self.mir.local_decls[local].mutability {
                        Mutability::Not => return,
                        Mutability::Mut => break, // needs check
                    }
                }
                Lvalue::Static(_) => {
                    // mutation of non-mut static is always
                    // illegal, but its checked earlier,
                    // independent of dataflow.
                    panic!("why are we checking about reassignment to static, context: {:?}",
                           context);
                }
            }
        }

        if let Some(mpi) = self.move_path_for_lvalue(context, move_data, lvalue) {
            if flow_state.inits.curr_state.contains(&mpi) {
                // may already be assigned before reaching this statement;
                // report error.
                self.report_illegal_mutation(context);
            }
        }
    }

    fn check_if_path_is_moved(&mut self,
                              context: Context,
                              lvalue: &Lvalue<'tcx>,
                              flow_state: &InProgress<'b, 'tcx>) {
        // FIXME: analogous code in check_loans first maps `lvalue` to
        // its base_path ... but is that what we want here?
        let lvalue = self.base_path(lvalue);

        let maybe_uninits = &flow_state.uninits;
        let move_data = maybe_uninits.base_results.operator().move_data();
        if let Some(mpi) = self.move_path_for_lvalue(context, move_data, lvalue) {
            if maybe_uninits.curr_state.contains(&mpi) {
                // find and report move(s) that could cause this to be uninitialized

                // FIXME: for each move in flow_state.move_outs ...
                &flow_state.move_outs;

                self.report_use_of_moved(context);
            } else {
                // sanity check: initialized on *some* path, right?
                assert!(flow_state.inits.curr_state.contains(&mpi));
            }
        }
    }

    fn move_path_for_lvalue(&mut self,
                            _context: Context,
                            move_data: &MoveData<'tcx>,
                            lvalue: &Lvalue<'tcx>)
                            -> Option<MovePathIndex>
    {
        // If returns None, then there is no move path corresponding
        // to a direct owner of `lvalue` (which means there is nothing
        // that borrowck tracks for its analysis).

        match move_data.rev_lookup.find(lvalue) {
            LookupResult::Parent(_) => None,
            LookupResult::Exact(mpi) => Some(mpi),
        }
    }

    fn check_if_assigned_path_is_moved(&mut self,
                                       context: Context,
                                       lvalue: &Lvalue<'tcx>,
                                       flow_state: &InProgress<'b, 'tcx>) {
        // recur down lvalue; dispatch to check_if_path_is_moved when necessary
        let mut lvalue = lvalue;
        loop {
            match *lvalue {
                Lvalue::Local(_) | Lvalue::Static(_) => {
                    // assigning to `x` does not require `x` be initialized.
                    break;
                }
                Lvalue::Projection(ref proj) => {
                    let Projection { ref base, ref elem } = **proj;
                    match *elem {
                        ProjectionElem::Deref |
                        // assigning to *P requires `P` initialized.
                        ProjectionElem::Index(_/*operand*/) |
                        ProjectionElem::ConstantIndex { .. } |
                        // assigning to P[i] requires `P` initialized.
                        ProjectionElem::Downcast(_/*adt_def*/, _/*variant_idx*/) =>
                        // assigning to (P->variant) is okay if assigning to `P` is okay
                        //
                        // FIXME: is this true even if P is a adt with a dtor?
                        { }

                        ProjectionElem::Subslice { .. } => {
                            panic!("we dont allow assignments to subslices, context: {:?}", context);
                        }

                        ProjectionElem::Field(..) => {
                            // if type of `P` has a dtor, then
                            // assigning to `P.f` requires `P` itself
                            // be already initialized
                            let tcx = self.bcx.tcx;
                            match base.ty(self.mir, tcx).to_ty(tcx).sty {
                                ty::TyAdt(def, _) if def.has_dtor(tcx) => {

                                    // FIXME: analogous code in
                                    // check_loans.rs first maps
                                    // `base` to its base_path.

                                    self.check_if_path_is_moved(context,
                                                                base, flow_state);

                                    // (base initialized; no need to
                                    // recur further)
                                    break;
                                }
                                _ => {}
                            }
                        }
                    }

                    lvalue = base;
                    continue;
                }
            }
        }
    }

    fn check_for_conflicting_loan(&mut self,
                                  context: Context,
                                  _location: Location,
                                  _bk: BorrowKind,
                                  _lvalue: &Lvalue<'tcx>,
                                  flow_state: &InProgress<'b, 'tcx>) {
        // NOTE FIXME: The analogous code in old borrowck
        // check_loans.rs is careful to iterate over every *issued*
        // loan, as opposed to just the in scope ones.
        //
        // (Or if you prefer, all the *other* iterations over loans
        // only consider loans that are in scope of some given
        // CodeExtent)
        //
        // The (currently skeletal) code here does not encode such a
        // distinction, which means it is almost certainly over
        // looking something.
        //
        // (It is probably going to reject code that should be
        // accepted, I suspect, by treated issued-but-out-of-scope
        // loans as issued-and-in-scope, and thus causing them to
        // interfere with other loans.)
        //
        // However, I just want to get something running, especially
        // since I am trying to move into new territory with NLL, so
        // lets get this going first, and then address the issued vs
        // in-scope distinction later.

        let state = &flow_state.borrows;
        let data = &state.base_results.operator().borrows();

        // does any loan generated here, conflict with a previously issued loan?
        for gen in state.elems_generated().map(|g| &data[g]) {
            for issued in state.elems_incoming().map(|i| &data[i]) {
                if self.conflicts_with(gen, issued) {
                    self.report_conflicting_borrow(context);
                }
            }
        }

        // does any loan generated here conflict with another loan also generated here?
        for (gen1, gen2) in state.pairs_generated().map(|(g1, g2)| (&data[g1], &data[g2])) {
            if self.conflicts_with(gen1, gen2) {
                self.report_conflicting_borrow(context);
            }
        }
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn report_use_of_moved(&mut self, context: Context) {
        if true { panic!("use of moved data, context: {:?}", context); }
        unimplemented!()
    }

    fn report_use_while_borrowed(&mut self, context: Context) {
        if true { panic!("use of borrowed data, context: {:?}", context); }
        unimplemented!()
    }

    fn report_conflicting_borrow(&mut self, context: Context) {
        if true { panic!("conflicting borrows, context: {:?}", context); }
        unimplemented!()
    }

    fn report_illegal_mutation(&mut self, context: Context) {
        if true { panic!("illegal mutation, context: {:?}", context); }
        unimplemented!()
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    // FIXME: needs to be able to express errors analogous to check_loans.rs
    fn conflicts_with(&self, loan1: &BorrowData<'tcx>, loan2: &BorrowData<'tcx>) -> bool {
        if loan1.compatible_with(loan2.kind) { return false; }

        let loan2_base_path = self.base_path(&loan2.lvalue);
        for restricted in self.restrictions(&loan1.lvalue) {
            if restricted != loan2_base_path { continue; }
            return true;
        }

        let loan1_base_path = self.base_path(&loan1.lvalue);
        for restricted in self.restrictions(&loan2.lvalue) {
            if restricted != loan1_base_path { continue; }
            return true;
        }

        return false;
    }

    // FIXME (#16118): function intended to allow the borrow checker
    // to be less precise in its handling of Box while still allowing
    // moves out of a Box. They should be removed when/if we stop
    // treating Box specially (e.g. when/if DerefMove is added...)

    fn base_path<'c>(&self, lvalue: &'c Lvalue<'tcx>) -> &'c Lvalue<'tcx> {
        //! Returns the base of the leftmost (deepest) dereference of an
        //! Box in `lvalue`. If there is no dereference of an Box
        //! in `lvalue`, then it just returns `lvalue` itself.

        let mut cursor = lvalue;
        let mut deepest = lvalue;
        loop {
            let proj = match *cursor {
                Lvalue::Local(..) | Lvalue::Static(..) => return deepest,
                Lvalue::Projection(ref proj) => proj,
            };
            if proj.elem == ProjectionElem::Deref &&
                lvalue.ty(self.mir, self.bcx.tcx).to_ty(self.bcx.tcx).is_box()
            {
                deepest = &proj.base;
            }
            cursor = &proj.base;
        }
    }
}

impl<'tcx> BorrowData<'tcx> {
    fn compatible_with(&self, bk: BorrowKind) -> bool {
        match (self.kind, bk) {
            (BorrowKind::Shared, BorrowKind::Shared) => true,

            (BorrowKind::Mut, _) |
            (BorrowKind::Unique, _) |
            (_, BorrowKind::Mut) |
            (_, BorrowKind::Unique) => false,
        }
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn each_borrow_involving_path<F>(&mut self,
                                     _context: Context,
                                     lvalue: &Lvalue<'tcx>,
                                     flow_state: &InProgress<'b, 'tcx>,
                                     mut op: F)
        where F: FnMut(&mut Self, BorrowIndex, &BorrowData<'tcx>)
    {
        // FIXME: analogous code in check_loans first maps `lvalue` to
        // its base_path.

        let domain = flow_state.borrows.base_results.operator();
        let data = domain.borrows();

        // check for loan restricting path P being used. Accounts for
        // borrows of P, P.a.b, etc.
        for i in flow_state.borrows.elems_incoming() {
            // FIXME: check_loans.rs filtered this to "in scope"
            // loans; i.e. it took a scope S and checked that each
            // restriction's kill_scope was a superscope of S.
            let borrowed = &data[i];
            for restricted in self.restrictions(&borrowed.lvalue) {
                if restricted == lvalue {
                    op(self, i, borrowed);
                }
            }
        }

        // check for loans (not restrictions) on any base path.
        // e.g. Rejects `{ let x = &mut a.b; let y = a.b.c; }`,
        // since that moves out of borrowed path `a.b`.
        //
        // Limiting to loans (not restrictions) keeps this one
        // working: `{ let x = &mut a.b; let y = a.c; }`
        let mut cursor = lvalue;
        loop {
            // FIXME: check_loans.rs invoked `op` *before* cursor
            // shift here.  Might just work (and even avoid redundant
            // errors?) given code above?  But for now, I want to try
            // doing what I think is more "natural" check.
            for i in flow_state.borrows.elems_incoming() {
                let borrowed = &data[i];
                if borrowed.lvalue == *cursor {
                    op(self, i, borrowed);
                }
            }

            match *cursor {
                Lvalue::Local(_) | Lvalue::Static(_) => break,
                Lvalue::Projection(ref proj) => cursor = &proj.base,
            }
        }
    }
}

struct Restrictions<'c, 'tcx: 'c> {
    mir: &'c Mir<'tcx>,
    tcx: TyCtxt<'c, 'tcx, 'tcx>,
    lvalue_stack: Vec<&'c Lvalue<'tcx>>,
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn restrictions<'c>(&self,
                        lvalue: &'c Lvalue<'tcx>)
                        -> Restrictions<'c, 'tcx> where 'b: 'c
    {
        Restrictions { lvalue_stack: vec![lvalue], mir: self.mir, tcx: self.bcx.tcx }
    }
}

impl<'c, 'tcx> Iterator for Restrictions<'c, 'tcx> {
    type Item = &'c Lvalue<'tcx>;
    fn next(&mut self) -> Option<Self::Item> {
        'pop: loop {
            let lvalue = match self.lvalue_stack.pop() {
                None => return None,
                Some(lvalue) => lvalue,
            };

            // `lvalue` may not be a restriction itself, but may hold
            // one further down (e.g. we never return downcasts here,
            // but may return a base of a downcast).
            //
            // Also, we need to enqueue any additional subrestrictions
            // that it implies, since we can only return from from
            // this call alone.

            let mut cursor = lvalue;
            'cursor: loop {
                let proj = match *cursor {
                    Lvalue::Local(_) => return Some(cursor), // search yielded this leaf
                    Lvalue::Static(_) => continue 'pop, // fruitless leaf; try next on stack
                    Lvalue::Projection(ref proj) => proj,
                };

                match proj.elem {
                    ProjectionElem::Field(_/*field*/, _/*ty*/) => {
                        // FIXME: add union handling
                        cursor = &proj.base;
                        continue 'cursor;
                    }
                    ProjectionElem::Downcast(..) |
                    ProjectionElem::Subslice { .. } |
                    ProjectionElem::ConstantIndex { .. } |
                    ProjectionElem::Index(Operand::Constant(..)) => {
                        cursor = &proj.base;
                        continue 'cursor;
                    }
                    ProjectionElem::Index(Operand::Consume(ref index)) => {
                        self.lvalue_stack.push(index);
                        cursor = &proj.base;
                        continue 'cursor;
                    }
                    ProjectionElem::Deref => {
                        // (handled below)
                    }
                }

                assert_eq!(proj.elem, ProjectionElem::Deref);

                let ty = proj.base.ty(self.mir, self.tcx).to_ty(self.tcx);
                match ty.sty {
                    ty::TyRawPtr(_) => {
                        // borrowck ignores raw ptrs; treat analogous to imm borrow
                        continue 'pop;
                    }
                    // R-Deref-Imm-Borrowed
                    ty::TyRef(_/*rgn*/, ty::TypeAndMut { ty: _, mutbl: hir::MutImmutable }) => {
                        // immutably-borrowed referents do not have
                        // recursively-implied restrictions (because
                        // preventing actions on `*LV` does nothing
                        // about aliases like `*LV1`)

                        // FIXME: do I need to check validity of `_r`
                        // here though? (I think the original
                        // check_loans code did, like the readme says)

                        // (And do I *really* not have to recursively
                        // process the `base` as a further search
                        // here? Leaving this `if false` here as a
                        // hint to look at this again later.
                        //
                        // Ah, it might be because the restrictions
                        // are distinct from the path
                        // substructure. Note that there is a separate
                        // loop over the path substructure in fn
                        // each_borrow_involving_path, for better or
                        // for worse.

                        if false {
                            cursor = &proj.base;
                            continue 'cursor;
                        } else {
                            continue 'pop;
                        }
                    }

                    // R-Deref-Mut-Borrowed
                    ty::TyRef(_/*rgn*/, ty::TypeAndMut { ty: _, mutbl: hir::MutMutable }) => {
                        // mutably-borrowed referents are themselves
                        // restricted.

                        // FIXME: do I need to check validity of `_r`
                        // here though? (I think the original
                        // check_loans code did, like the readme says)

                        // schedule base for future iteration.
                        self.lvalue_stack.push(&proj.base);
                        return Some(cursor); // search yielded interior node
                    }

                    // R-Deref-Send-Pointer
                    ty::TyAdt(..) if ty.is_box() => {
                        // borrowing interior of a box implies that
                        // its base can no longer be mutated (o/w box
                        // storage would be freed)
                        self.lvalue_stack.push(&proj.base);
                        return Some(cursor); // search yielded interior node
                    }

                    _ => panic!("unknown type fed to Projection Deref."),
                }
            }
        }
    }
}

