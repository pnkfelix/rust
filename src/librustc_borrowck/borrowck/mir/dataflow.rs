// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use syntax::attr::AttrMetaMethods;

use rustc::ty::TyCtxt;
use rustc::mir::repr::{self, Mir};

use std::fmt::Debug;
use std::io;
use std::marker::PhantomData;
use std::mem;
use std::usize;

use super::{MirBorrowckCtxtPreDataflow};
use super::gather_moves::{Location, MoveData, MoveOut};
use super::gather_moves::{MovePath, MovePathData, MovePathIndex, MoveOutIndex, PathMap};
use super::graphviz;
use bitslice::BitSlice; // adds set_bit/get_bit to &[usize] bitvector rep.

pub trait Dataflow {
    fn dataflow(&mut self);
}

impl<'b, 'a: 'b, 'tcx: 'a, BD> Dataflow for MirBorrowckCtxtPreDataflow<'b, 'a, 'tcx, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>, BD::Bit: Debug

{
    fn dataflow(&mut self) {
        self.flow_state.build_gen_and_kill_sets();
        self.pre_dataflow_instrumentation().unwrap();
        self.flow_state.propagate();
        self.post_dataflow_instrumentation().unwrap();
    }
}

struct PropagationContext<'c, 'b: 'c, 'tcx: 'b, O, OnReturn>
    where O: 'c + BitDenotation<Ctxt=MoveData<'tcx>>,
          OnReturn: Fn(&MoveData, &mut [usize], &repr::Lvalue)
{
    builder: &'c mut DataflowStateBuilder<'b, 'tcx, O>,
    changed: bool,
    on_return: OnReturn
}

impl<'a, 'tcx: 'a, BD> DataflowStateBuilder<'a, 'tcx, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>
{
    fn propagate(&mut self) {
        let mut temp = vec![0; self.flow_state.sets.words_per_block];
        let mut propcx = PropagationContext {
            builder: self,
            changed: true,
            on_return: |move_data, in_out, dest_lval| {
                let move_path_index = move_data.rev_lookup.find(dest_lval);
                on_all_children_bits(in_out,
                                     &move_data.path_map,
                                     &move_data.move_paths,
                                     move_path_index,
                                     &|in_out, mpi| {
                                         in_out.clear_bit(mpi.idx());
                                     });
            },
        };
        while propcx.changed {
            propcx.changed = false;
            propcx.reset(&mut temp);
            propcx.walk_cfg(&mut temp);
        }
    }
}

impl<'a, 'tcx: 'a, BD> DataflowStateBuilder<'a, 'tcx, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>
{
    fn build_gen_and_kill_sets(&mut self) {
        // First we need to build the gen- and kill-sets. The
        // gather_moves information provides a high-level mapping from
        // mir-locations to the MoveOuts (and those correspond
        // directly to gen-sets here). But we still need to figure out
        // the kill-sets.

        let move_data = &self.move_data;

        for bb in self.mir.all_basic_blocks() {
            let &repr::BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
                self.mir.basic_block_data(bb);

            let sets = &mut self.flow_state.sets.for_block(bb.index());

            for j_stmt in statements.iter().enumerate() {
                self.flow_state.operator.statement_effect(&self.move_data, sets, bb, j_stmt);
            }

            if let Some(ref term) = *terminator {
                let stmts_len = statements.len();
                self.flow_state.operator.terminator_effect(&self.move_data, sets, bb, (stmts_len, term));
            }
        }
    }
}

fn on_all_children_bits<Each>(set: &mut [usize],
                              path_map: &PathMap,
                              move_paths: &MovePathData,
                              move_path_index: MovePathIndex,
                              each_child: &Each)
    where Each: Fn(&mut [usize], MoveOutIndex)
{
    // 1. invoke `each_child` callback for all moves that directly
    //    influence path for `move_path_index`
    for move_index in &path_map[move_path_index] {
        each_child(set, *move_index);
    }

    // 2. for each child of the path (that is named in this
    //    function), recur.
    //
    // (Unnamed children are irrelevant to dataflow; by
    // definition they have no associated moves.)
    let mut next_child_index = move_paths[move_path_index].first_child;
    while let Some(child_index) = next_child_index {
        on_all_children_bits(set, path_map, move_paths, child_index, each_child);
        next_child_index = move_paths[child_index].next_sibling;
    }
}

impl<'c, 'b: 'c, 'tcx: 'b, O, OnReturn> PropagationContext<'c, 'b, 'tcx, O, OnReturn>
    where O: BitDenotation<Ctxt=MoveData<'tcx>>,
          OnReturn: Fn(&MoveData, &mut [usize], &repr::Lvalue)
{
    fn reset(&mut self, bits: &mut [usize]) {
        let e = if O::initial_value() {usize::MAX} else {0};
        for b in bits {
            *b = e;
        }
    }

    fn walk_cfg(&mut self, in_out: &mut [usize]) {
        let mir = self.builder.mir;
        for (bb_idx, bb_data) in mir.basic_blocks.iter().enumerate() {
            let ref mut builder = &mut self.builder;
            {
                let sets = builder.flow_state.sets.for_block(bb_idx);
                debug_assert!(in_out.len() == sets.on_entry.len());
                in_out.clone_from_slice(sets.on_entry);
                bitwise(in_out, sets.gen_set, &Union);
                bitwise(in_out, sets.kill_set, &Subtract);
            }
            builder.propagate_bits_into_graph_successors_of(in_out,
                                                            &mut self.changed,
                                                            (repr::BasicBlock::new(bb_idx), bb_data),
                                                            &self.on_return);
        }
    }
}

impl<'b, 'a: 'b, 'tcx: 'a, BD> MirBorrowckCtxtPreDataflow<'b, 'a, 'tcx, BD>
    where BD: BitDenotation<Ctxt=MoveData<'tcx>>,
          BD::Bit: Debug
{
    fn pre_dataflow_instrumentation(&self) -> io::Result<()> {
        self.if_attr_meta_name_found(
            "borrowck_graphviz_preflow",
            |this, path: &str| {
                graphviz::print_borrowck_graph_to(this, "preflow", path)
            })
    }

    fn post_dataflow_instrumentation(&self) -> io::Result<()> {
        self.if_attr_meta_name_found(
            "borrowck_graphviz_postflow",
            |this, path: &str| {
                graphviz::print_borrowck_graph_to(this, "postflow", path)
            })
    }

    fn if_attr_meta_name_found<F>(&self,
                                  name: &str,
                                  callback: F) -> io::Result<()>
        where F: for <'aa, 'bb> FnOnce(&'aa Self, &'bb str) -> io::Result<()>
    {
        for attr in self.attributes {
            if attr.check_name("rustc_mir") {
                let items = attr.meta_item_list();
                for item in items.iter().flat_map(|l| l.iter()) {
                    if item.check_name(name) {
                        if let Some(s) = item.value_str() {
                            return callback(self, &s);
                        } else {
                            self.bcx.tcx.sess.span_err(
                                item.span,
                                &format!("{} attribute requires a path", item.name()));
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

/// Maps each block to a set of bits
#[derive(Clone, Debug)]
struct Bits {
    bits: Vec<usize>,
}

impl Bits {
    fn new(init_word: usize, num_words: usize) -> Self {
        Bits { bits: vec![init_word; num_words] }
    }
}

pub struct DataflowStateBuilder<'a, 'tcx: 'a, O>
    where O: BitDenotation<Ctxt=MoveData<'tcx>>
{
    pub flow_state: DataflowState<O>,
    pub move_data: MoveData<'tcx>,
    pub mir: &'a Mir<'tcx>,
}

pub struct DataflowState<O: BitDenotation>
{
    /// All the sets for the analysis. (Factored into its
    /// own structure so that we can borrow it mutably
    /// on its own separate from other fields.)
    pub sets: AllSets,

    /// operator used to initialize, combine, and interpret bits.
    operator: O,
}

impl<'a, 'tcx: 'a, O> DataflowStateBuilder<'a, 'tcx, O>
    where O: BitDenotation<Ctxt=MoveData<'tcx>>
{
    pub fn unpack(self) -> (MoveData<'tcx>, DataflowState<O>) {
        (self.move_data, self.flow_state)
    }
}

pub struct AllSets {
    /// Analysis bitwidth for each block.
    bits_per_block: usize,

    /// Number of words associated with each block entry
    /// equal to bits_per_block / usize::BITS, rounded up.
    words_per_block: usize,

    /// For each block, bits generated by executing the statements in
    /// the block. (For comparison, the Terminator for each block is
    /// handled in a flow-specific manner during propagation.)
    gen_sets: Bits,

    /// For each block, bits killed by executing the statements in the
    /// block. (For comparison, the Terminator for each block is
    /// handled in a flow-specific manner during propagation.)
    kill_sets: Bits,

    /// For each block, bits valid on entry to the block.
    on_entry_sets: Bits,
}

pub struct BlockSets<'a> {
    on_entry: &'a mut [usize],
    gen_set: &'a mut [usize],
    kill_set: &'a mut [usize],
}

impl AllSets {
    pub fn bytes_per_block(&self) -> usize { (self.bits_per_block + 7) / 8 }
    pub fn for_block(&mut self, block_idx: usize) -> BlockSets {
        let offset = self.words_per_block * block_idx;
        let range = offset..(offset + self.words_per_block);
        BlockSets {
            on_entry: &mut self.on_entry_sets.bits[range.clone()],
            gen_set: &mut self.gen_sets.bits[range.clone()],
            kill_set: &mut self.kill_sets.bits[range],
        }
    }

    fn lookup_set_for<'a>(&self, sets: &'a Bits, block_idx: usize) -> &'a [usize] {
        let offset = self.words_per_block * block_idx;
        &sets.bits[offset..(offset + self.words_per_block)]
    }
    pub fn gen_set_for(&self, block_idx: usize) -> &[usize] {
        self.lookup_set_for(&self.gen_sets, block_idx)
    }
    pub fn kill_set_for(&self, block_idx: usize) -> &[usize] {
        self.lookup_set_for(&self.kill_sets, block_idx)
    }
    pub fn on_entry_set_for(&self, block_idx: usize) -> &[usize] {
        self.lookup_set_for(&self.on_entry_sets, block_idx)
    }
}

fn for_each_bit<F>(bits_per_block: usize, words: &[usize], mut f: F)
    where F: FnMut(usize) {
    //! Helper for iterating over the bits in a bitvector.

    for (word_index, &word) in words.iter().enumerate() {
        if word != 0 {
            let usize_bits: usize = mem::size_of::<usize>();
            let base_index = word_index * usize_bits;
            for offset in 0..usize_bits {
                let bit = 1 << offset;
                if (word & bit) != 0 {
                    // NB: we round up the total number of bits
                    // that we store in any given bit set so that
                    // it is an even multiple of usize::BITS. This
                    // means that there may be some stray bits at
                    // the end that do not correspond to any
                    // actual value; that's why we first check
                    // that we are in range of bits_per_block.
                    let bit_index = base_index + offset as usize;
                    if bit_index >= bits_per_block {
                        return;
                    } else {
                        f(bit_index);
                    }
                }
            }
        }
    }
}

impl<O> DataflowState<O>
    where O: BitDenotation
{
    pub fn each_bit<F>(&self, ctxt: &O::Ctxt, words: &[usize], f: F) where F: FnMut(usize) {
        for_each_bit(self.operator.bits_per_block(ctxt), words, f)
    }

    pub fn interpret_set<'c>(&self, ctxt: &'c O::Ctxt, words: &[usize]) -> Vec<&'c O::Bit> {
        let mut v = Vec::new();
        self.each_bit(ctxt, words, |i| {
            v.push(self.operator.interpret(ctxt, i));
        });
        v
    }
}

pub trait BitwiseOperator {
    /// Joins two predecessor bits together, typically either `|` or `&`
    fn join(&self, pred1: usize, pred2: usize) -> usize;
}

/// Parameterization for the precise form of data flow that is used.
pub trait DataflowOperator : BitwiseOperator {
    /// Specifies the initial value for each bit in the `on_entry` set
    fn initial_value() -> bool;
}

pub trait BitDenotation: DataflowOperator {
    /// Specifies what is represented by each bit in the dataflow bitvector.
    type Bit;

    /// Specifies what, if any, separate context needs to be supplied for methods below.
    type Ctxt;

    /// Size of each bivector allocated for each block in the analysis.
    fn bits_per_block(&self,
                      ctxt: &Self::Ctxt) -> usize;

    /// Provides the meaning of each entry in the dataflow bitvector.
    /// (Mostly intended for use for better debug instrumentation.)
    fn interpret<'a>(&self, &'a Self::Ctxt, idx: usize) -> &'a Self::Bit;

    /// Mutates the block-sets (the flow sets for the given
    /// basic block) according to the effects of evaluating statement.
    ///
    /// This is used, in particular, for building up the
    /// "transfer-function" represnting the overall-effect of the
    /// block, represented via GEN and KILL sets.
    ///
    /// The statement here is `idx_stmt.1`; `idx_stmt.0` is just
    /// an identifying index: namely, the index of the statement
    /// in the basic block.
    fn statement_effect(&self,
                        ctxt: &Self::Ctxt,
                        sets: &mut BlockSets,
                        bb: repr::BasicBlock,
                        idx_stmt: (usize, &repr::Statement));

    /// Mutates the block-sets (the flow sets for the given
    /// basic block) according to the effects of evaluating
    /// the terminator.
    ///
    /// This is used, in particular, for building up the
    /// "transfer-function" represnting the overall-effect of the
    /// block, represented via GEN and KILL sets.
    ///
    /// The terminator here is `idx_term.1`; `idx_term.0` is just an
    /// identifying index: namely, the number of statements in `bb`
    /// itself.
    ///
    /// The effects applied here cannot depend on which branch the
    /// terminator took.
    fn terminator_effect(&self,
                         ctxt: &Self::Ctxt,
                         sets: &mut BlockSets,
                         bb: repr::BasicBlock,
                         idx_term: (usize, &repr::Terminator));

    /// Mutates the block-sets according to the (flow-dependent)
    /// effect of a successful return from a Call terminator.
    ///
    /// If basic-block BB_x ends with a call-instruction that, upon
    /// successful return, flows to BB_y, then this method will be
    /// called on the exit flow-state of BB_x in order to set up the
    /// entry flow-state of BB_y.
    ///
    /// This is used, in particular, as a special case during the
    /// "propagate" loop where all of the basic blocks are repeatedly
    /// visited. Since the effects of a Call terminator are
    /// flow-dependent, the current MIR cannot encode them via just
    /// GEN and KILL sets attached to the block, and so instead we add
    /// this extra machinery to represent the flow-dependent effect.
    ///
    /// Note: as a historical artifact, this currently takes as input
    /// the *entire* packed collection of bitvectors in `in_out`.  We
    /// might want to look into narrowing that to something more
    /// specific, just to make the interface more self-documenting.
    fn propagate_call_return(&self,
                             ctxt: &Self::Ctxt,
                             in_out: &mut [usize],
                             call_bb: repr::BasicBlock,
                             dest_bb: repr::BasicBlock,
                             dest_lval: &repr::Lvalue);
}

impl<'a, BO: BitwiseOperator> BitwiseOperator for &'a BO {
    fn join(&self, pred1: usize, pred2: usize) -> usize { (*self).join(pred1, pred2) }
}

impl<'a, DO: DataflowOperator> DataflowOperator for &'a DO {
    fn initial_value() -> bool { DO::initial_value() }
}

/*
impl<'a, BD: BitDenotation> BitDenotation for &'a BD {
    type Bit = BD::Bit;
    type Ctxt = BD::Ctxt;
    fn bits_per_block(&self, ctxt: &Self::Ctxt) -> usize {
        (*self).bits_per_block(ctxt)
    }
    fn interpret<'b>(&self, ctxt: &'b Self::Ctxt, idx: usize) -> &'b Self::Bit {
        (*self).interpret(ctxt, idx)
    }
}
*/

impl<'a, 'tcx: 'a, D> DataflowStateBuilder<'a, 'tcx, D>
    where D: BitDenotation<Ctxt=MoveData<'tcx>>
{
    pub fn new(mir: &'a Mir<'tcx>,
               move_data: MoveData<'tcx>,
               denotation: D) -> Self {
        let bits_per_block = denotation.bits_per_block(&move_data);
        let usize_bits = mem::size_of::<usize>() * 8;
        let words_per_block = (bits_per_block + usize_bits - 1) / usize_bits;
        let num_blocks = mir.basic_blocks.len();
        let num_words = num_blocks * words_per_block;

        let entry = if D::initial_value() { usize::MAX } else {0};

        let zeroes = Bits::new(0, num_words);
        let on_entry = Bits::new(entry, num_words);

        DataflowStateBuilder {
            flow_state: DataflowState {
                sets: AllSets {
                    bits_per_block: bits_per_block,
                    words_per_block: words_per_block,
                    gen_sets: zeroes.clone(),
                    kill_sets: zeroes,
                    on_entry_sets: on_entry,
                },
                operator: denotation,
            },
            move_data: move_data,
            mir: mir,
        }
    }
}

impl<'a, 'tcx: 'a, D> DataflowStateBuilder<'a, 'tcx, D>
    where D: BitDenotation<Ctxt=MoveData<'tcx>>
{
    /// Propagates the bits of `in_out` into all the successors of `bb`,
    /// using bitwise operator denoted by `self.operator`.
    ///
    /// For most blocks, this is entirely uniform. However, for blocks
    /// that end with a call terminator, the effect of the call on the
    /// dataflow state may depend on whether the call returned
    /// successfully or unwound. To reflect this, the `on_return`
    /// callback mutates `in_out` when propagating `in_out` via a call
    /// terminator; such mutation is performed *last*, to ensure its
    /// side-effects do not leak elsewhere (e.g. into unwind target).
    fn propagate_bits_into_graph_successors_of<OnReturn>(
        &mut self,
        in_out: &mut [usize],
        changed: &mut bool,
        (bb, bb_data): (repr::BasicBlock, &repr::BasicBlockData),
        on_return: OnReturn) where OnReturn: Fn(&MoveData, &mut [usize], &repr::Lvalue)
    {
        match bb.terminator().kind {
            repr::TerminatorKind::Return |
            repr::TerminatorKind::Resume => {}
            repr::TerminatorKind::Goto { ref target } |
            repr::TerminatorKind::Drop { ref target, value: _, unwind: None } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, target);
            }
            repr::TerminatorKind::Drop { ref target, value: _, unwind: Some(ref unwind) } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, target);
                self.propagate_bits_into_entry_set_for(in_out, changed, unwind);
            }
            repr::TerminatorKind::If { ref targets, .. } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, &targets.0);
                self.propagate_bits_into_entry_set_for(in_out, changed, &targets.1);
            }
            repr::TerminatorKind::Switch { ref targets, .. } |
            repr::TerminatorKind::SwitchInt { ref targets, .. } => {
                for target in targets {
                    self.propagate_bits_into_entry_set_for(in_out, changed, target);
                }
            }
            repr::TerminatorKind::Call { ref cleanup, ref destination, func: _, args: _ } => {
                if let Some(ref unwind) = *cleanup {
                    self.propagate_bits_into_entry_set_for(in_out, changed, unwind);
                }
                if let Some((ref dest_lval, ref dest_bb)) = *destination {
                    // N.B.: This must be done *last*, after all other
                    // propagation, as documented in comment above.
                    self.flow_state.operator.propagate_call_return(
                        &self.move_data, in_out, bb, *dest_bb, dest_lval);
                    self.propagate_bits_into_entry_set_for(in_out, changed, dest_bb);
                }
            }
        }
    }

    fn propagate_bits_into_entry_set_for(&mut self,
                                         in_out: &[usize],
                                         changed: &mut bool,
                                         bb: &repr::BasicBlock) {
        let entry_set = self.flow_state.sets.for_block(bb.index()).on_entry;
        let set_changed = bitwise(entry_set, in_out, &self.flow_state.operator);
        if set_changed {
            *changed = true;
        }
    }
}

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
#[derive(Default)]
pub struct MaybeInitializedLvals<'tcx> {
    // We need to attach a `'tcx` to this (zero-sized) structure so
    // that its `impl BitDenotation` can use `'tcx` when instantiating
    // its associated types. But all of the uses of `'tcx` are just
    // in MoveData context parameters that are passed to its methods,
    // so capture that usage here.
    phantom: PhantomData<for <'a> Fn(&'a MoveData<'tcx>)>,
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
#[derive(Default)]
pub struct MaybeUninitializedLvals<'tcx> {
    // We need to attach a `'tcx` to this (zero-sized) structure so
    // that its `impl BitDenotation` can use `'tcx` when instantiating
    // its associated types. But all of the uses of `'tcx` are just
    // in MoveData context parameters that are passed to its methods,
    // so capture that usage here.
    phantom: PhantomData<for <'a> Fn(&'a MoveData<'tcx>)>,
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
#[derive(Default)]
pub struct MovingOutStatements<'tcx> {
    // We need to attach a `'tcx` to this (zero-sized) structure so
    // that its `impl BitDenotation` can use `'tcx` when instantiating
    // its associated types. But all of the uses of `'tcx` are just
    // in MoveData context parameters that are passed to its methods,
    // so capture that usage here.
    phantom: PhantomData<for <'a> Fn(&'a MoveData<'tcx>)>,
}

trait MoveDataCarrier<'tcx> {
    fn move_data(&self) -> &MoveData<'tcx>;
}

impl<'tcx> BitDenotation for MovingOutStatements<'tcx> {
    type Bit = MoveOut;
    type Ctxt = MoveData<'tcx>;
    fn bits_per_block(&self, ctxt: &MoveData<'tcx>) -> usize {
        ctxt.moves.len()
    }
    fn interpret<'c>(&self, ctxt: &'c MoveData<'tcx>, idx: usize) -> &'c Self::Bit {
        &ctxt.moves[idx]
    }
    fn statement_effect(&self,
                        move_data: &Self::Ctxt,
                        sets: &mut BlockSets,
                        bb: repr::BasicBlock,
                        (idx, stmt): (usize, &repr::Statement)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;

        let loc = Location { block: bb, index: idx };
        debug!("stmt {:?} at loc {:?} moves out of move_indexes {:?}",
               stmt, loc, &loc_map[loc]);
        for move_index in &loc_map[loc] {
            // Every path deinitialized by a *particular move*
            // has corresponding bit, "gen'ed" (i.e. set)
            // here, in dataflow vector
            zero_to_one(&mut sets.gen_set, *move_index);
        }
        match stmt.kind {
            repr::StatementKind::Assign(ref lvalue, _) => {
                // assigning into this `lvalue` kills all
                // MoveOuts from it, and *also* all MoveOuts
                // for children and associated fragment sets.
                let move_path_index = rev_lookup.find(lvalue);

                on_all_children_bits(sets.kill_set,
                                     path_map,
                                     move_paths,
                                     move_path_index,
                                     &|kill_set, mpi| {
                                         kill_set.set_bit(mpi.idx());
                                     });
            }
        }
    }

    fn terminator_effect(&self,
                         move_data: &Self::Ctxt,
                         sets: &mut BlockSets,
                         bb: repr::BasicBlock,
                         (statements_len, term): (usize, &repr::Terminator)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;
        let loc = Location { block: bb, index: statements_len };
        debug!("terminator {:?} at loc {:?} moves out of move_indexes {:?}",
               term, loc, &loc_map[loc]);
        for move_index in &loc_map[loc] {
            zero_to_one(&mut sets.gen_set, *move_index);
        }
    }

    fn propagate_call_return(&self,
                             move_data: &Self::Ctxt,
                             in_out: &mut [usize],
                             call_bb: repr::BasicBlock,
                             dest_bb: repr::BasicBlock,
                             dest_lval: &repr::Lvalue) {
        let move_path_index = move_data.rev_lookup.find(dest_lval);
        on_all_children_bits(in_out,
                             &move_data.path_map,
                             &move_data.move_paths,
                             move_path_index,
                             &|in_out, mpi| {
                                 in_out.clear_bit(mpi.idx());
                             });
    }
}
fn zero_to_one(gen_set: &mut [usize], move_index: MoveOutIndex) {
    let retval = gen_set.set_bit(move_index.idx());
    assert!(retval);
}

fn move_outs_paths(move_data: &MoveData,
                   move_outs: &[MoveOutIndex]) -> Vec<MovePathIndex> {
    move_outs.iter()
        .map(|mi| move_data.moves[mi.idx()].path)
        .collect()
}

impl<'tcx> BitDenotation for MaybeInitializedLvals<'tcx> {
    type Bit = MovePath<'tcx>;
    type Ctxt = MoveData<'tcx>;
    fn bits_per_block(&self, ctxt: &Self::Ctxt) -> usize {
        ctxt.move_paths.len()
    }
    fn interpret<'c>(&self, ctxt: &'c Self::Ctxt, idx: usize) -> &'c Self::Bit {
        &ctxt.move_paths[MovePathIndex::new(idx)]
    }

    // gens bits for lvalues initialized by statement
    // kills bits for lvalues moved-out by statement
    fn statement_effect(&self,
                        move_data: &Self::Ctxt,
                        sets: &mut BlockSets,
                        bb: repr::BasicBlock,
                        (idx, stmt): (usize, &repr::Statement)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;

        let loc = Location { block: bb, index: idx };
        let move_outs = &loc_map[loc];

        // first, setup kill_set: kill bits for l-values moved out by
        // stmt (`path` intermediate vec is unecessary, but arguably
        // result debug! printout better reflects method's effects).
        let paths = move_outs_paths(move_data, &move_outs[..]);
        debug!("stmt {:?} at loc {:?} moves out of paths {:?}",
               stmt, loc, paths);
        for &move_path_index in &paths {
            // (don't use zero_to_one since bit may already be set to 1.)
            on_all_children_bits(sets.kill_set,
                                 path_map,
                                 move_paths,
                                 move_path_index,
                                 &|kill_set, mpi| {
                                     kill_set.set_bit(mpi.idx());
                                 });
        }

        // second, the gen_set: initialized l-values are generated,
        // and removed from kill_set (because dataflow will first
        // apply gen_set effects, followed by the kill_set effects).
        match stmt.kind {
            repr::StatementKind::Assign(ref lvalue, _) => {
                // assigning into `lvalue` gens a bit for it and *also*
                // all lvalues for children and associated fragment sets.
                //
                // also clear the corresponding bit in the kill set, if any
                let move_path_index = rev_lookup.find(lvalue);

                on_all_children_bits(sets.gen_set,
                                     path_map,
                                     move_paths,
                                     move_path_index,
                                     &|gen_set, mpi| {
                                         gen_set.set_bit(mpi.idx());
                                     });

                on_all_children_bits(sets.kill_set,
                                     path_map,
                                     move_paths,
                                     move_path_index,
                                     &|kill_set, mpi| {
                                         kill_set.clear_bit(mpi.idx());
                                     });
            }
        }
    }

    fn terminator_effect(&self,
                         move_data: &Self::Ctxt,
                         sets: &mut BlockSets,
                         bb: repr::BasicBlock,
                         (statements_len, term): (usize, &repr::Terminator)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;
        let loc = Location { block: bb, index: statements_len };
        let paths = move_outs_paths(move_data, &loc_map[loc]);
        debug!("terminator {:?} at loc {:?} moves out of paths {:?}",
               term, loc, &paths);
        for &move_path_index in &paths {
            // (don't use zero_to_one since bit may already be set to 1.)
            on_all_children_bits(sets.kill_set,
                                 path_map,
                                 move_paths,
                                 move_path_index,
                                 &|kill_set, mpi| {
                                     kill_set.set_bit(mpi.idx());
                                 });
        }
    }

    fn propagate_call_return(&self,
                             move_data: &Self::Ctxt,
                             in_out: &mut [usize],
                             call_bb: repr::BasicBlock,
                             dest_bb: repr::BasicBlock,
                             dest_lval: &repr::Lvalue) { 
        // when a call returns successfully, that means we need to set
        // the bits for that dest_lval to 1 (initialized).
        let move_path_index = move_data.rev_lookup.find(dest_lval);
        on_all_children_bits(in_out,
                             &move_data.path_map,
                             &move_data.move_paths,
                             move_path_index,
                             &|in_out, mpi| {
                                 in_out.set_bit(mpi.idx());
                             });
    }
}

impl<'tcx> BitDenotation for MaybeUninitializedLvals<'tcx> {
    type Bit = MovePath<'tcx>;
    type Ctxt = MoveData<'tcx>;
    fn bits_per_block(&self, ctxt: &Self::Ctxt) -> usize { ctxt.move_paths.len() }
    fn interpret<'c>(&self, ctxt: &'c Self::Ctxt, idx: usize) -> &'c Self::Bit { &ctxt.move_paths[MovePathIndex::new(idx)] }

    // gens bits for lvalues moved-out by statement
    // kills bits for lvalues initialized by statement
    fn statement_effect(&self,
                        move_data: &Self::Ctxt,
                        sets: &mut BlockSets,
                        bb: repr::BasicBlock,
                        (idx, stmt): (usize, &repr::Statement)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;

        let loc = Location { block: bb, index: idx };
        let move_outs = &loc_map[loc];

        // first, setup gen_set: gen bits for l-values moved out by
        // stmt (`path` intermediate vec is unecessary, but arguably
        // result debug! printout better reflects method's effects).
        let paths = move_outs_paths(move_data, &move_outs[..]);
        debug!("stmt {:?} at loc {:?} moves out of paths {:?}",
               stmt, loc, paths);
        for &move_path_index in &paths {
            // (don't use zero_to_one since bit may already be set to 1.)
            on_all_children_bits(sets.gen_set,
                                 path_map,
                                 move_paths,
                                 move_path_index,
                                 &|gen_set, mpi| {
                                     gen_set.set_bit(mpi.idx());
                                 });
        }

        // second, the kill_set: kill bits for initialized l-value, if any
        match stmt.kind {
            repr::StatementKind::Assign(ref lvalue, _) => {
                // assigning into `lvalue` gens a bit for it and *also*
                // all lvalues for children and associated fragment sets.
                //
                // also clear the corresponding bit in the kill set, if any
                let move_path_index = rev_lookup.find(lvalue);

                on_all_children_bits(sets.kill_set,
                                     path_map,
                                     move_paths,
                                     move_path_index,
                                     &|kill_set, mpi| {
                                         kill_set.set_bit(mpi.idx());
                                     });
            }
        }
    }

    fn terminator_effect(&self,
                         move_data: &Self::Ctxt,
                         sets: &mut BlockSets,
                         bb: repr::BasicBlock,
                         (statements_len, term): (usize, &repr::Terminator)) {
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;
        let loc = Location { block: bb, index: statements_len };
        let paths = move_outs_paths(move_data, &loc_map[loc]);
        debug!("terminator {:?} at loc {:?} moves out of paths {:?}",
               term, loc, paths);
        for &move_path_index in &paths[..] {
            // (don't use zero_to_one since bit may already be set to 1.)
            on_all_children_bits(sets.kill_set,
                                 path_map,
                                 move_paths,
                                 move_path_index,
                                 &|kill_set, mpi| {
                                     kill_set.set_bit(mpi.idx());
                                 });
        }
    }


    fn propagate_call_return(&self,
                             move_data: &Self::Ctxt,
                             in_out: &mut [usize],
                             call_bb: repr::BasicBlock,
                             dest_bb: repr::BasicBlock,
                             dest_lval: &repr::Lvalue) {
        // when a call returns successfully, that means we need to
        // clear the bits for that (definitely initialized) dest_lval.
        let move_path_index = move_data.rev_lookup.find(dest_lval);
        on_all_children_bits(in_out,
                             &move_data.path_map,
                             &move_data.move_paths,
                             move_path_index,
                             &|in_out, mpi| {
                                 in_out.clear_bit(mpi.idx());
                             });
    }
}

impl<'tcx> BitwiseOperator for MovingOutStatements<'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // moves from both preds are in scope
    }
}

impl<'tcx> BitwiseOperator for MaybeInitializedLvals<'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // "maybe" means we union effects of both preds
    }
}

impl<'tcx> BitwiseOperator for MaybeUninitializedLvals<'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // "maybe" means we union effects of both preds
    }
}

impl<'tcx> DataflowOperator for MovingOutStatements<'tcx> {
    #[inline] fn initial_value() -> bool { false } // no loans in scope by default
}

impl<'tcx> DataflowOperator for MaybeInitializedLvals<'tcx> {
    #[inline] fn initial_value() -> bool { false } // lvalues start uninitialized
}

impl<'tcx> DataflowOperator for MaybeUninitializedLvals<'tcx> {
    #[inline] fn initial_value() -> bool { true } // lvalues start uninitialized
}

#[inline]
fn bitwise<Op:BitwiseOperator>(out_vec: &mut [usize],
                               in_vec: &[usize],
                               op: &Op) -> bool {
    assert_eq!(out_vec.len(), in_vec.len());
    let mut changed = false;
    for (out_elt, in_elt) in out_vec.iter_mut().zip(in_vec) {
        let old_val = *out_elt;
        let new_val = op.join(old_val, *in_elt);
        *out_elt = new_val;
        changed |= old_val != new_val;
    }
    changed
}

struct Union;
impl BitwiseOperator for Union {
    fn join(&self, a: usize, b: usize) -> usize { a | b }
}
struct Subtract;
impl BitwiseOperator for Subtract {
    fn join(&self, a: usize, b: usize) -> usize { a & !b }
}
