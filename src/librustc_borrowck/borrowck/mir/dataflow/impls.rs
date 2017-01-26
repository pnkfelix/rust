// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::ty::{Region, TyCtxt};
use rustc::middle::region::{CodeExtent, CodeExtentData};
use rustc::mir::{self, Mir, Location};
use rustc::mir::visit::Visitor;
use rustc::util::nodemap::{FxHashMap, FxHashSet};
use rustc_data_structures::bitslice::BitSlice; // adds set_bit/get_bit to &[usize] bitvector rep.
use rustc_data_structures::bitslice::{BitwiseOperator};
use rustc_data_structures::indexed_set::{IdxSet};
use rustc_data_structures::indexed_vec::{Idx, IndexVec};

use super::super::gather_moves::{HasMoveData, MoveData, MoveOutIndex, DataPathIndex};
use super::super::MoveDataParamEnv;
use super::super::DropFlagState;
use super::super::drop_flag_effects_for_function_entry;
use super::super::drop_flag_effects_for_location;
use super::super::on_lookup_result_bits;

use super::{BitDenotation, BlockSets, DataflowOperator};

// Dataflow analyses are built upon some interpretation of the
// bitvectors attached to each basic block, represented via a
// zero-sized structure.

/// `MaybeInitializedLvals` tracks all l-values that might be
/// initialized upon reaching a particular point in the control flow
/// for a function.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                       // maybe-init:
///                                            // {}
///     let a = S; let b = S; let c; let d;    // {a, b}
///
///     if pred {
///         drop(a);                           // {   b}
///         b = S;                             // {   b}
///
///     } else {
///         drop(b);                           // {a}
///         d = S;                             // {a,       d}
///
///     }                                      // {a, b,    d}
///
///     c = S;                                 // {a, b, c, d}
/// }
/// ```
///
/// To determine whether an l-value *must* be initialized at a
/// particular control-flow point, one can take the set-difference
/// between this data and the data from `MaybeUninitializedLvals` at the
/// corresponding control-flow point.
///
/// Similarly, at a given `drop` statement, the set-intersection
/// between this data and `MaybeUninitializedLvals` yields the set of
/// l-values that would require a dynamic drop-flag at that statement.
pub struct MaybeInitializedLvals<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
}

impl<'a, 'tcx: 'a> MaybeInitializedLvals<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>,
               mir: &'a Mir<'tcx>,
               mdpe: &'a MoveDataParamEnv<'tcx>)
               -> Self
    {
        MaybeInitializedLvals { tcx: tcx, mir: mir, mdpe: mdpe }
    }
}

impl<'a, 'tcx: 'a> HasMoveData<'tcx> for MaybeInitializedLvals<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> { &self.mdpe.move_data }
}

/// `MaybeUninitializedLvals` tracks all l-values that might be
/// uninitialized upon reaching a particular point in the control flow
/// for a function.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                       // maybe-uninit:
///                                            // {a, b, c, d}
///     let a = S; let b = S; let c; let d;    // {      c, d}
///
///     if pred {
///         drop(a);                           // {a,    c, d}
///         b = S;                             // {a,    c, d}
///
///     } else {
///         drop(b);                           // {   b, c, d}
///         d = S;                             // {   b, c   }
///
///     }                                      // {a, b, c, d}
///
///     c = S;                                 // {a, b,    d}
/// }
/// ```
///
/// To determine whether an l-value *must* be uninitialized at a
/// particular control-flow point, one can take the set-difference
/// between this data and the data from `MaybeInitializedLvals` at the
/// corresponding control-flow point.
///
/// Similarly, at a given `drop` statement, the set-intersection
/// between this data and `MaybeInitializedLvals` yields the set of
/// l-values that would require a dynamic drop-flag at that statement.
pub struct MaybeUninitializedLvals<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
}

impl<'a, 'tcx: 'a> MaybeUninitializedLvals<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>,
               mir: &'a Mir<'tcx>,
               mdpe: &'a MoveDataParamEnv<'tcx>)
               -> Self
    {
        MaybeUninitializedLvals { tcx: tcx, mir: mir, mdpe: mdpe }
    }
}

impl<'a, 'tcx: 'a> HasMoveData<'tcx> for MaybeUninitializedLvals<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> { &self.mdpe.move_data }
}

/// `DefinitelyInitializedLvals` tracks all l-values that are definitely
/// initialized upon reaching a particular point in the control flow
/// for a function.
///
/// FIXME: Note that once flow-analysis is complete, this should be
/// the set-complement of MaybeUninitializedLvals; thus we can get rid
/// of one or the other of these two. I'm inclined to get rid of
/// MaybeUninitializedLvals, simply because the sets will tend to be
/// smaller in this analysis and thus easier for humans to process
/// when debugging.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                       // definite-init:
///                                            // {          }
///     let a = S; let b = S; let c; let d;    // {a, b      }
///
///     if pred {
///         drop(a);                           // {   b,     }
///         b = S;                             // {   b,     }
///
///     } else {
///         drop(b);                           // {a,        }
///         d = S;                             // {a,       d}
///
///     }                                      // {          }
///
///     c = S;                                 // {       c  }
/// }
/// ```
///
/// To determine whether an l-value *may* be uninitialized at a
/// particular control-flow point, one can take the set-complement
/// of this data.
///
/// Similarly, at a given `drop` statement, the set-difference between
/// this data and `MaybeInitializedLvals` yields the set of l-values
/// that would require a dynamic drop-flag at that statement.
pub struct DefinitelyInitializedLvals<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
}

impl<'a, 'tcx: 'a> DefinitelyInitializedLvals<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>,
               mir: &'a Mir<'tcx>,
               mdpe: &'a MoveDataParamEnv<'tcx>)
               -> Self
    {
        DefinitelyInitializedLvals { tcx: tcx, mir: mir, mdpe: mdpe }
    }
}

impl<'a, 'tcx: 'a> HasMoveData<'tcx> for DefinitelyInitializedLvals<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> { &self.mdpe.move_data }
}

/// `MovingOutStatements` tracks the statements that perform moves out
/// of particular l-values. More precisely, it tracks whether the
/// *effect* of such moves (namely, the uninitialization of the
/// l-value in question) can reach some point in the control-flow of
/// the function, or if that effect is "killed" by some intervening
/// operation reinitializing that l-value.
///
/// The resulting dataflow is a more enriched version of
/// `MaybeUninitializedLvals`. Both structures on their own only tell
/// you if an l-value *might* be uninitialized at a given point in the
/// control flow. But `MovingOutStatements` also includes the added
/// data of *which* particular statement causing the deinitialization
/// that the borrow checker's error meessage may need to report.
#[allow(dead_code)]
pub struct MovingOutStatements<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
}

impl<'a, 'tcx> HasMoveData<'tcx> for MovingOutStatements<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> { &self.mdpe.move_data }
}

/// `Extents` tracks the code extents (i.e. statically determined
/// regions). Extents are introduced by borrows and are terminated by
/// `EndRegion` statements.
pub struct Extents<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
}

impl<'a, 'tcx> Extents<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, mir: &'a Mir<'tcx>) -> Self {
        Extents { tcx: tcx, mir: mir }
    }
    pub fn code_extent_data(&self, e: CodeExtent) -> CodeExtentData {
        self.tcx.region_maps.code_extent_data(e)
    }
}

// (In principle BorrowIdx need not be pub, but since it is associated
// type of BitDenotation impl, hand is forced by privacy rules.)

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BorrowIdx(usize);

impl Idx for BorrowIdx {
    fn new(idx: usize) -> Self { BorrowIdx(idx) }
    fn index(self) -> usize { self.0 }
}

// `Borrows` maps each dataflow bit to an `Rvalue::Ref`, which can be
// uniquely identified in the MIR by the `Location` of the assigment
// statement in which it appears on the right hand side.
pub struct Borrows<'a, 'tcx: 'a> {
    #[allow(dead_code)]
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    locations: IndexVec<BorrowIdx, Location>,
    loc_map: FxHashMap<Location, BorrowIdx>,
    ext_map: FxHashMap<CodeExtent, FxHashSet<BorrowIdx>>,
}

impl<'a, 'tcx> Borrows<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, mir: &'a Mir<'tcx>) -> Self {
        let mut visitor = GatherBorrows { idx_vec: IndexVec::new(),
                                          loc_map: FxHashMap(),
                                          ext_map: FxHashMap(), };
        visitor.visit_mir(mir);
        return Borrows { tcx: tcx,
                         mir: mir,
                         locations: visitor.idx_vec,
                         loc_map: visitor.loc_map,
                         ext_map: visitor.ext_map, };

        struct GatherBorrows {
            idx_vec: IndexVec<BorrowIdx, Location>,
            loc_map: FxHashMap<Location, BorrowIdx>,
            ext_map: FxHashMap<CodeExtent, FxHashSet<BorrowIdx>>,
        }
        impl<'tcx> Visitor<'tcx> for GatherBorrows {
            fn visit_rvalue(&mut self,
                            rvalue: &mir::Rvalue,
                            location: mir::Location) {
                if let mir::Rvalue::Ref(&Region::ReScope(ref extent), _, _) = *rvalue {
                    let idx = self.idx_vec.push(location);
                    self.loc_map.insert(location, idx);
                    let mut borrows = self.ext_map.entry(*extent).or_insert(FxHashSet());
                    borrows.insert(idx);
                }
            }
        }
    }
    pub fn location(&self, idx: BorrowIdx) -> &Location {
        &self.locations[idx]
    }
}

impl<'a, 'tcx> MaybeInitializedLvals<'a, 'tcx> {
    fn update_bits(sets: &mut BlockSets<DataPathIndex>, path: DataPathIndex,
                   state: DropFlagState)
    {
        match state {
            DropFlagState::Absent => sets.kill(&path),
            DropFlagState::Present => sets.gen(&path),
        }
    }
}

impl<'a, 'tcx> MaybeUninitializedLvals<'a, 'tcx> {
    fn update_bits(sets: &mut BlockSets<DataPathIndex>, path: DataPathIndex,
                   state: DropFlagState)
    {
        match state {
            DropFlagState::Absent => sets.gen(&path),
            DropFlagState::Present => sets.kill(&path),
        }
    }
}

impl<'a, 'tcx> DefinitelyInitializedLvals<'a, 'tcx> {
    fn update_bits(sets: &mut BlockSets<DataPathIndex>, path: DataPathIndex,
                   state: DropFlagState)
    {
        match state {
            DropFlagState::Absent => sets.kill(&path),
            DropFlagState::Present => sets.gen(&path),
        }
    }
}

impl<'a, 'tcx> BitDenotation for MaybeInitializedLvals<'a, 'tcx> {
    type Idx = DataPathIndex;
    fn name() -> &'static str { "maybe_init" }
    fn bits_per_block(&self) -> usize {
        self.move_data().data_paths.len()
    }

    fn start_block_effect(&self, sets: &mut BlockSets<DataPathIndex>)
    {
        drop_flag_effects_for_function_entry(
            self.tcx, self.mir, self.mdpe,
            |path, s| {
                assert!(s == DropFlagState::Present);
                sets.on_entry.add(&path);
            });
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<DataPathIndex>,
                        bb: mir::BasicBlock,
                        idx: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: idx },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<DataPathIndex>,
                         bb: mir::BasicBlock,
                         statements_len: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: statements_len },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn propagate_call_return(&self,
                             in_out: &mut IdxSet<DataPathIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             dest_lval: &mir::Lvalue) {
        // when a call returns successfully, that means we need to set
        // the bits for that dest_lval to 1 (initialized).
        on_lookup_result_bits(self.tcx, self.mir, self.move_data(),
                              self.move_data().rev_lookup.find(dest_lval),
                              |mpi| { in_out.add(&mpi); });
    }
}

impl<'a, 'tcx> BitDenotation for MaybeUninitializedLvals<'a, 'tcx> {
    type Idx = DataPathIndex;
    fn name() -> &'static str { "maybe_uninit" }
    fn bits_per_block(&self) -> usize {
        self.move_data().data_paths.len()
    }

    // sets on_entry bits for Arg lvalues
    fn start_block_effect(&self, sets: &mut BlockSets<DataPathIndex>) {
        // set all bits to 1 (uninit) before gathering counterevidence
        for e in sets.on_entry.words_mut() { *e = !0; }

        drop_flag_effects_for_function_entry(
            self.tcx, self.mir, self.mdpe,
            |path, s| {
                assert!(s == DropFlagState::Present);
                sets.on_entry.remove(&path);
            });
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<DataPathIndex>,
                        bb: mir::BasicBlock,
                        idx: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: idx },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<DataPathIndex>,
                         bb: mir::BasicBlock,
                         statements_len: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: statements_len },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn propagate_call_return(&self,
                             in_out: &mut IdxSet<DataPathIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             dest_lval: &mir::Lvalue) {
        // when a call returns successfully, that means we need to set
        // the bits for that dest_lval to 0 (initialized).
        on_lookup_result_bits(self.tcx, self.mir, self.move_data(),
                              self.move_data().rev_lookup.find(dest_lval),
                              |mpi| { in_out.remove(&mpi); });
    }
}

impl<'a, 'tcx> BitDenotation for DefinitelyInitializedLvals<'a, 'tcx> {
    type Idx = DataPathIndex;
    fn name() -> &'static str { "definite_init" }
    fn bits_per_block(&self) -> usize {
        self.move_data().data_paths.len()
    }

    // sets on_entry bits for Arg lvalues
    fn start_block_effect(&self, sets: &mut BlockSets<DataPathIndex>) {
        for e in sets.on_entry.words_mut() { *e = 0; }

        drop_flag_effects_for_function_entry(
            self.tcx, self.mir, self.mdpe,
            |path, s| {
                assert!(s == DropFlagState::Present);
                sets.on_entry.add(&path);
            });
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<DataPathIndex>,
                        bb: mir::BasicBlock,
                        idx: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: idx },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<DataPathIndex>,
                         bb: mir::BasicBlock,
                         statements_len: usize)
    {
        drop_flag_effects_for_location(
            self.tcx, self.mir, self.mdpe,
            Location { block: bb, statement_index: statements_len },
            |path, s| Self::update_bits(sets, path, s)
        )
    }

    fn propagate_call_return(&self,
                             in_out: &mut IdxSet<DataPathIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             dest_lval: &mir::Lvalue) {
        // when a call returns successfully, that means we need to set
        // the bits for that dest_lval to 1 (initialized).
        on_lookup_result_bits(self.tcx, self.mir, self.move_data(),
                              self.move_data().rev_lookup.find(dest_lval),
                              |mpi| { in_out.add(&mpi); });
    }
}

impl<'a, 'tcx> BitDenotation for MovingOutStatements<'a, 'tcx> {
    type Idx = MoveOutIndex;
    fn name() -> &'static str { "moving_out" }
    fn bits_per_block(&self) -> usize {
        self.move_data().moves.len()
    }

    fn start_block_effect(&self, _sets: &mut BlockSets<MoveOutIndex>) {
        // no move-statements have been executed prior to function
        // execution, so this method has no effect on `_sets`.
    }
    fn statement_effect(&self,
                        sets: &mut BlockSets<MoveOutIndex>,
                        bb: mir::BasicBlock,
                        idx: usize) {
        let (tcx, mir, move_data) = (self.tcx, self.mir, self.move_data());
        let stmt = &mir[bb].statements[idx];
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;

        let loc = Location { block: bb, statement_index: idx };
        debug!("stmt {:?} at loc {:?} moves out of move_indexes {:?}",
               stmt, loc, &loc_map[loc]);
        for move_index in &loc_map[loc] {
            // Every path deinitialized by a *particular move*
            // has corresponding bit, "gen'ed" (i.e. set)
            // here, in dataflow vector
            zero_to_one(sets.gen_set.words_mut(), *move_index);
        }
        let bits_per_block = self.bits_per_block();
        match stmt.kind {
            mir::StatementKind::SetDiscriminant { .. } => {
                span_bug!(stmt.source_info.span, "SetDiscriminant should not exist in borrowck");
            }
            mir::StatementKind::Assign(ref lvalue, _) => {
                // assigning into this `lvalue` kills all
                // MoveOuts from it, and *also* all MoveOuts
                // for children and associated fragment sets.
                on_lookup_result_bits(tcx,
                                     mir,
                                     move_data,
                                     rev_lookup.find(lvalue),
                                     |mpi| for moi in &path_map[mpi] {
                                         assert!(moi.index() < bits_per_block);
                                         sets.kill_set.add(&moi);
                                     });
            }
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::EndRegion(_) |
            mir::StatementKind::Nop => {}
        }
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<MoveOutIndex>,
                         bb: mir::BasicBlock,
                         statements_len: usize)
    {
        let (mir, move_data) = (self.mir, self.move_data());
        let term = mir[bb].terminator();
        let loc_map = &move_data.loc_map;
        let loc = Location { block: bb, statement_index: statements_len };
        debug!("terminator {:?} at loc {:?} moves out of move_indexes {:?}",
               term, loc, &loc_map[loc]);
        let bits_per_block = self.bits_per_block();
        for move_index in &loc_map[loc] {
            assert!(move_index.index() < bits_per_block);
            zero_to_one(sets.gen_set.words_mut(), *move_index);
        }
    }

    fn propagate_call_return(&self,
                             in_out: &mut IdxSet<MoveOutIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             dest_lval: &mir::Lvalue) {
        let move_data = self.move_data();
        let bits_per_block = self.bits_per_block();

        let path_map = &move_data.path_map;
        on_lookup_result_bits(self.tcx,
                              self.mir,
                              move_data,
                              move_data.rev_lookup.find(dest_lval),
                              |mpi| for moi in &path_map[mpi] {
                                  assert!(moi.index() < bits_per_block);
                                  in_out.remove(&moi);
                              });
    }
}

impl<'a, 'tcx> BitDenotation for Extents<'a, 'tcx> {
    type Idx = CodeExtent;
    fn name() -> &'static str { "extents" }
    fn bits_per_block(&self) -> usize {
        self.tcx.region_maps.code_extents_len()
    }

    fn start_block_effect(&self, _sets: &mut BlockSets<CodeExtent>) {
        // no code extents have been entered prior to function
        // execution, so this method has no effect on `_sets`.
        //
        // FIXME: is the above true? Shouldn't we at least initiate
        // the CallSiteScope, and perhaps also the ParameterScope?
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<CodeExtent>,
                        bb: mir::BasicBlock,
                        stmt_idx: usize) {
        let block = &self.mir[bb];
        let stmt = block.statements.get(stmt_idx).unwrap();
        match stmt.kind {
            mir::StatementKind::Assign(
                _ /*lvalue_dest*/,
                ref rvalue) =>
            {
                if let mir::Rvalue::Ref(&Region::ReScope(ref extent),
                                        _ /*borrow_kind*/,
                                        _ /*lvalue_source*/) = *rvalue {
                    sets.gen(extent);
                }
            }

            mir::StatementKind::EndRegion(ref extents) =>
            {
                for extent in extents {
                    sets.kill(extent);
                }
            }

            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Nop |
            mir::StatementKind::SetDiscriminant { lvalue: _, variant_index: _ } => {
                // no borrows occur in these cases
            }
        }
    }

    fn terminator_effect(&self,
                         _sets: &mut BlockSets<CodeExtent>,
                         _bb: mir::BasicBlock,
                         _statements_len: usize) {
        // no terminators start nor end code extents.
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<CodeExtent>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             _dest_lval: &mir::Lvalue) {
        // there are no effects on the extents from method calls.
    }
}

impl<'a, 'tcx> BitDenotation for Borrows<'a, 'tcx> {
    type Idx = BorrowIdx;
    fn name() -> &'static str { "borrows" }
    fn bits_per_block(&self) -> usize {
        self.locations.len()
    }
    fn start_block_effect(&self, _sets: &mut BlockSets<BorrowIdx>)  {
        // no borrows of code extents have been taken prior to
        // function execution, so this method has no effect on
        // `_sets`.
    }
    fn statement_effect(&self,
                        sets: &mut BlockSets<BorrowIdx>,
                        bb: mir::BasicBlock,
                        stmt_idx: usize) {
        let block = &self.mir[bb];
        let stmt = block.statements.get(stmt_idx).unwrap();
        match stmt.kind {
            mir::StatementKind::EndRegion(ref extents) => {
                for ext in extents {
                    for idx in &self.ext_map[ext] {
                        sets.kill(&idx);
                    }
                }
            }

            mir::StatementKind::Assign(_, ref rhs) => {
                if let mir::Rvalue::Ref(&Region::ReScope(extent), _, _) = *rhs {
                    let loc = mir::Location { block: bb, statement_index: stmt_idx };
                    let idx = self.loc_map[&loc];
                    assert!(self.ext_map.get(&extent).unwrap().contains(&idx));
                    sets.gen(&idx);
                }
            }

            mir::StatementKind::SetDiscriminant { .. } |
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Nop => {}

        }
    }
    fn terminator_effect(&self,
                         _sets: &mut BlockSets<BorrowIdx>,
                         _bb: mir::BasicBlock,
                         _statements_len: usize) {
        // no terminators start nor end code extents.
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<BorrowIdx>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             _dest_lval: &mir::Lvalue) {
        // there are no effects on the extents from method calls.
    }
}

fn zero_to_one(bitvec: &mut [usize], move_index: MoveOutIndex) {
    let retval = bitvec.set_bit(move_index.index());
    assert!(retval);
}

impl<'a, 'tcx> BitwiseOperator for MovingOutStatements<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // moves from both preds are in scope
    }
}

impl<'a, 'tcx> BitwiseOperator for MaybeInitializedLvals<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // "maybe" means we union effects of both preds
    }
}

impl<'a, 'tcx> BitwiseOperator for MaybeUninitializedLvals<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // "maybe" means we union effects of both preds
    }
}

impl<'a, 'tcx> BitwiseOperator for DefinitelyInitializedLvals<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 & pred2 // "definitely" means we intersect effects of both preds
    }
}

impl<'a, 'tcx> BitwiseOperator for Extents<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // union effects of preds when computing extents
    }
}

impl<'a, 'tcx> BitwiseOperator for Borrows<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // union effects of preds when computing borrows
    }
}

// The way that dataflow fixed point iteration works, you want to
// start at bottom and work your way to a fixed point. Control-flow
// merges will apply the `join` operator to each block entry's current
// state (which starts at that bottom value).
//
// This means, for propagation across the graph, that you either want
// to start at all-zeroes and then use Union as your merge when
// propagating, or you start at all-ones and then use Intersect as
// your merge when propagating.

impl<'a, 'tcx> DataflowOperator for MovingOutStatements<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = no loans in scope by default
    }
}

impl<'a, 'tcx> DataflowOperator for MaybeInitializedLvals<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = uninitialized
    }
}

impl<'a, 'tcx> DataflowOperator for MaybeUninitializedLvals<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = initialized (start_block_effect counters this at outset)
    }
}

impl<'a, 'tcx> DataflowOperator for DefinitelyInitializedLvals<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        true // bottom = initialized (start_block_effect counters this at outset)
    }
}

impl<'a, 'tcx> DataflowOperator for Extents<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = no regions borrowed by default
    }
}

impl<'a, 'tcx> DataflowOperator for Borrows<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = no Rvalue::Refs are active by default
    }
}
