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

use rustc::middle::ty;
use rustc::mir::repr::{self, Mir};

use std::io;
use std::mem;
use std::usize;

use super::MirBorrowckCtxt;
use super::gather_moves::{Location, MoveData, MovePathData, MovePathIndex, PathMap};
use super::graphviz;

pub trait BitSlice {
    fn set_bit(&mut self, idx: usize) -> bool;
    fn get_bit(&self, idx: usize) -> bool;
}

impl BitSlice for [usize] {
    fn set_bit(&mut self, idx: usize) -> bool { set_bit(self, idx) }
    fn get_bit(&self, idx: usize) -> bool { get_bit(self, idx) }
}

struct BitLookup { word: usize, bit_in_word: usize, bit_mask: usize }

#[inline]
fn bit_lookup(bit: usize) -> BitLookup {
    let usize_bits = mem::size_of::<usize>() * 8;
    let word = bit / usize_bits;
    let bit_in_word = bit % usize_bits;
    let bit_mask = 1 << bit_in_word;
    BitLookup { word: word, bit_in_word: bit_in_word, bit_mask: bit_mask }
}

fn get_bit(words: &[usize], bit: usize) -> bool {
    let BitLookup { word, bit_mask, .. } = bit_lookup(bit);
    (words[word] & bit_mask) != 0
}

fn set_bit(words: &mut [usize], bit: usize) -> bool {
    debug!("set_bit: words={} bit={}",
           bits_to_string(words, words.len() * mem::size_of::<usize>()), bit_str(bit));
    let BitLookup { word, bit_in_word, bit_mask } = bit_lookup(bit);
    debug!("word={} bit_in_word={} bit_mask={}", word, bit_in_word, bit_mask);
    let oldv = words[word];
    let newv = oldv | bit_mask;
    words[word] = newv;
    oldv != newv
}

fn bit_str(bit: usize) -> String {
    let byte = bit >> 8;
    let lobits = 1 << (bit & 0xFF);
    format!("[{}:{}-{:02x}]", bit, byte, lobits)
}

pub trait Dataflow {
    fn dataflow(&mut self);
}

impl<'b, 'a: 'b, 'tcx: 'a> Dataflow for MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn dataflow(&mut self) {
        self.build_gen_and_kill_sets();
        self.pre_dataflow_instrumentation().unwrap();
        self.propagate();
        self.post_dataflow_instrumentation().unwrap();
    }
}

struct PropagationContext<'c, 'b: 'c, 'a: 'b, 'tcx: 'a> {
    mbcx: &'c mut MirBorrowckCtxt<'b, 'a, 'tcx>,
    changed: bool,
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
    fn propagate(&mut self) {
        let mut temp = vec![0; self.flow_state.sets.words_per_block];
        let mut propcx = PropagationContext { mbcx: &mut *self, changed: true, };
        while propcx.changed {
            propcx.changed = false;
            propcx.reset(&mut temp);
            propcx.walk_cfg(&mut temp);
        }
    }

    fn build_gen_and_kill_sets(&mut self) {
        // First we need to build the gen- and kill-sets. The
        // gather_moves information provides a high-level mapping from
        // mir-locations to the MoveOuts (and those correspond
        // directly to gen-sets here). But we still need to figure out
        // the kill-sets.

        let move_data = &self.flow_state.operator;
        let move_paths = &move_data.move_paths;
        let loc_map = &move_data.loc_map;
        let path_map = &move_data.path_map;
        let rev_lookup = &move_data.rev_lookup;

        for bb in self.mir.all_basic_blocks() {
            let &repr::BasicBlockData { ref statements,
                                        ref terminator,
                                        is_cleanup: _ } =
                self.mir.basic_block_data(bb);

            let mut sets = self.flow_state.sets.for_block(bb.index());
            for (j, stmt) in statements.iter().enumerate() {
                let loc = Location { block: bb, index: j };
                debug!("stmt {:?} at loc {:?} moves out of move_indexes {:?}",
                       stmt, loc, &loc_map[loc]);
                for move_index in &loc_map[loc] {
                    // Every path deinitialized by a *particular move*
                    // has corresponding bit, "gen'ed" (i.e. set)
                    // here, in dataflow vector
                    let retval = sets.gen_set.set_bit(move_index.idx().unwrap());
                    assert!(retval);
                }
                match stmt.kind {
                    repr::StatementKind::Assign(ref lvalue, _) => {
                        // assigning into this `lvalue` kills all
                        // MoveOuts from it, and *also* all MoveOuts
                        // for children and associated fragment sets.
                        let move_path_index = rev_lookup.find(lvalue);
                        set_children_kill_bits(sets.kill_set,
                                               move_path_index,
                                               path_map,
                                               move_paths);
                    }
                }
            }

            let loc = Location { block: bb, index: statements.len() };
            debug!("terminator {:?} at loc {:?} moves out of move_indexes {:?}",
                   terminator, loc, &loc_map[loc]);
            for move_index in &loc_map[loc] {
                let retval = sets.gen_set.set_bit(move_index.idx().unwrap());
                assert!(retval);
            }

            // Note: while below as originally authored could be
            // written as an `if let`, it is more future-proof (to MIR
            // changes) to use an explicit `match` here.
            match *terminator {
                None => {}
                Some(repr::Terminator::Goto { target: _ }) => {}
                Some(repr::Terminator::If { cond: _, targets: _ }) => {}
                Some(repr::Terminator::Switch { discr: _, adt_def: _, targets: _ }) => {}
                Some(repr::Terminator::SwitchInt { discr: _, switch_ty: _, values: _, targets: _ }) => {}
                Some(repr::Terminator::Resume) => {}
                Some(repr::Terminator::Return) => {}
                Some(repr::Terminator::Drop { value: _, target: _, unwind: _ }) => {
                    // either kind of Drop completely invalidates the
                    // state of the referenced memory, effectively
                    // acting like a MoveOut. Such gen-set additions
                    // were added by the loop above over the loc_map.
                }
                Some(repr::Terminator::Call { func: _, args: _, cleanup: _,
                                              ref destination }) => {
                    // FIXME: I want this to reflect that the
                    // destination will be initialized if the call
                    // succeeds (thus killling any MoveOuts for that
                    // destination).
                    //
                    // For now, I will just do the kills
                    // unconditionally; I believe this matches the
                    // behavior of the old borrowck dataflow
                    // analysis. But in principle, it might be better
                    // to try to encode the branch-dependent
                    // transfer-function in some manner.

                    if let Some((ref destination, ref bb)) = *destination {
                        let move_path_index = rev_lookup.find(destination);
                        set_children_kill_bits(sets.kill_set,
                                               move_path_index,
                                               path_map,
                                               move_paths);
                    }
                }
            }
        }

        fn set_children_kill_bits(kill_set: &mut [usize],
                                  move_path_index: MovePathIndex,
                                  path_map: &PathMap,
                                  move_paths: &MovePathData) {
            assert!(move_path_index.idx().is_some());

            // 1. set kill bits for all moves that directly
            // influence path for `move_path_index`
            for move_index in &path_map[move_path_index] {
                kill_set.set_bit(move_index.idx().unwrap());
            }

            // 2. for each child of the path (that is named in this
            //    function), recur.
            //
            // (Unnamed children are irrelevant to dataflow; by
            // definition they have no associated moves.)
            let mut child_index = move_paths[move_path_index].first_child;
            while let Some(_) = child_index.idx() {
                set_children_kill_bits(kill_set, child_index, path_map, move_paths);
                child_index = move_paths[child_index].next_sibling;
            }
        }
    }
}

impl<'c, 'b: 'c, 'a: 'b, 'tcx: 'a> PropagationContext<'c, 'b, 'a, 'tcx> {
    fn reset(&mut self, bits: &mut [usize]) {
        let e = if self.mbcx.flow_state.operator.initial_value() {usize::MAX} else {0};
        for b in bits {
            *b = e;
        }
    }

    fn walk_cfg(&mut self, in_out: &mut [usize]) {
        let &mut MirBorrowckCtxt { ref mir, ref mut flow_state, .. } = self.mbcx;
        for (idx, bb) in mir.basic_blocks.iter().enumerate() {
            {
                let mut sets = flow_state.sets.for_block(idx);
                debug_assert!(in_out.len() == sets.on_entry.len());
                in_out.clone_from_slice(sets.on_entry);
                bitwise(in_out, sets.gen_set, &Union);
                bitwise(in_out, sets.kill_set, &Subtract);
            }
            flow_state.propagate_bits_into_graph_successors_of(in_out, &mut self.changed, bb);
        }
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> MirBorrowckCtxt<'b, 'a, 'tcx> {
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
        println!("MirBorrowckCtxt::if_attr_meta_name_found({}, callback)",
                 name);
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

pub struct DataflowState<O: BitDenotation>
{
    /// All the sets for the analysis. (Factored into its
    /// own structure so that we can borrow it mutably
    /// on its own separate from other fields.)
    pub sets: AllSets,

    /// operator used to initialize, combine, and interpret bits.
    operator: O,
}

pub struct AllSets {
    /// Analysis bitwidth for each block.
    bits_per_block: usize,

    /// Number of words associated with each block entry
    /// equal to bits_per_block / usize::BITS, rounded up.
    words_per_block: usize,

    /// for each block, bits generated by executing the block.
    /// FIXME what is role of Terminator here? flow-target-dependent?
    gen_sets: Bits,

    /// for each block, bits killed by executing the block.
    /// FIXME what is role of Terminator here? flow-target-dependent?
    kill_sets: Bits,

    /// for each block, bits valid on entry to the block.
    on_entry_sets: Bits,
}

pub struct BlockSets<'a> {
    on_entry: &'a mut [usize],
    gen_set: &'a mut [usize],
    kill_set: &'a mut [usize],
}

impl AllSets {
    pub fn bits_per_block(&self) -> usize { self.bits_per_block }
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

impl<O: BitDenotation> DataflowState<O> {
    fn each_bit<F>(&self, words: &[usize], mut f: F) -> bool
        where F: FnMut(usize) -> bool {
        //! Helper for iterating over the bits in a bitvector.
        //! Returns false on the first call to `f` that returns false;
        //! if all calls to `f` return true, then returns true.

        for (word_index, &word) in words.iter().enumerate() {
            if word != 0 {
                let base_index = word_index * usize::BITS;
                for offset in 0..usize::BITS {
                    let bit = 1 << offset;
                    if (word & bit) != 0 {
                        // NB: we round up the total number of bits
                        // that we store in any given bit set so that
                        // it is an even multiple of usize::BITS.  This
                        // means that there may be some stray bits at
                        // the end that do not correspond to any
                        // actual value.  So before we callback, check
                        // whether the bit_index is greater than the
                        // actual value the user specified and stop
                        // iterating if so.
                        let bit_index = base_index + offset as usize;
                        if bit_index >= self.sets.bits_per_block {
                            return true;
                        } else if !f(bit_index) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    pub fn interpret_set(&self, words: &[usize]) -> Vec<&O::Bit> {
        let mut v = Vec::new();
        self.each_bit(words, |i| {
            v.push(self.operator.interpret(i));
            true
        });
        v
    }
}

pub fn bits_to_string(words: &[usize], bytes: usize) -> String {
    let mut result = String::new();
    let mut sep = '[';

    // Note: this is a little endian printout of bytes.

    let mut i = 0;
    for &word in words.iter() {
        let mut v = word;
        for _ in 0..mem::size_of::<usize>() {
            let byte = v & 0xFF;
            if i >= bytes {
                assert!(byte == 0);
            } else {
                result.push(sep);
                result.push_str(&format!("{:02x}", byte));
            }
            v >>= 8;
            i += 1;
            sep = '-';
        }
    }
    result.push(']');
    return result
}

pub trait BitwiseOperator {
    /// Joins two predecessor bits together, typically either `|` or `&`
    fn join(&self, pred1: usize, pred2: usize) -> usize;
}

/// Parameterization for the precise form of data flow that is used.
pub trait DataflowOperator : BitwiseOperator {
    /// Specifies the initial value for each bit in the `on_entry` set
    fn initial_value(&self) -> bool;
}

pub trait BitDenotation: DataflowOperator {
    /// Specifies what is represented by each bit in the dataflow bitvector.
    type Bit;
    /// Size of each bivector allocated for each block in the analysis.
    fn bits_per_block(&self) -> usize;
    /// Provides the meaning of each entry in the dataflow bitvector.
    /// (Mostly intended for use for better debug instrumentation.)
    fn interpret(&self, idx: usize) -> &Self::Bit;
}

impl<D: BitDenotation> DataflowState<D> {
    pub fn new(mir: &Mir, denotation: D) -> Self {
        let bits_per_block = denotation.bits_per_block();
        let usize_bits = mem::size_of::<usize>() * 8;
        let words_per_block = (bits_per_block + usize_bits - 1) / usize_bits;
        let num_blocks = mir.basic_blocks.len();
        let num_words = num_blocks * words_per_block;

        let entry = if denotation.initial_value() { usize::MAX } else {0};

        let zeroes = Bits::new(0, num_words);
        let on_entry = Bits::new(entry, num_words);

        DataflowState {
            sets: AllSets {
                bits_per_block: bits_per_block,
                words_per_block: words_per_block,
                gen_sets: zeroes.clone(),
                kill_sets: zeroes,
                on_entry_sets: on_entry,
            },
            operator: denotation,
        }
    }
}

impl<D: BitDenotation> DataflowState<D> {
    fn propagate_bits_into_graph_successors_of(&mut self,
                                               in_out: &mut [usize],
                                               changed: &mut bool,
                                               bb: &repr::BasicBlockData) {
        let term = if let Some(ref term) = bb.terminator { term } else { return };
        match *term {
            repr::Terminator::Return |
            repr::Terminator::Resume => {}
            repr::Terminator::Goto { ref target } |
            repr::Terminator::Drop { ref target, value: _, unwind: None } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, target);
            }
            repr::Terminator::Drop { ref target, value: _, unwind: Some(ref unwind) } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, target);
                self.propagate_bits_into_entry_set_for(in_out, changed, unwind);
            }
            repr::Terminator::If { ref targets, .. } => {
                self.propagate_bits_into_entry_set_for(in_out, changed, &targets.0);
                self.propagate_bits_into_entry_set_for(in_out, changed, &targets.1);
            }
            repr::Terminator::Switch { ref targets, .. } |
            repr::Terminator::SwitchInt { ref targets, .. } => {
                for target in targets {
                    self.propagate_bits_into_entry_set_for(in_out, changed, target);
                }
            }
            repr::Terminator::Call { ref cleanup, ref destination, ref func, ref args } => {
                if let Some(ref unwind) = *cleanup {
                    self.propagate_bits_into_entry_set_for(in_out, changed, unwind);
                }
                if let Some((_, ref destination)) = *destination {
                    self.propagate_bits_into_entry_set_for(in_out, changed, destination);
                }
            }
        }
    }

    fn propagate_bits_into_entry_set_for(&mut self,
                                         in_out: &mut [usize],
                                         changed: &mut bool,
                                         bb: &repr::BasicBlock) {
        let entry_set = self.sets.for_block(bb.index()).on_entry;
        let set_changed = bitwise(entry_set, in_out, &self.operator);
        if set_changed {
            *changed = true;
        }
    }
}


impl<'a, 'tcx:'a> DataflowState<MoveData<'a, 'tcx>> {
    pub fn new_move_analysis(mir: &'a Mir<'tcx>, tcx: &ty::ctxt<'tcx>) -> Self {
        let move_data = MoveData::gather_moves(mir, tcx);
        DataflowState::new(mir, move_data)
    }
}

impl<'a, 'tcx> BitwiseOperator for MoveData<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // moves from both preds are in scope
    }
}

impl<'a, 'tcx> DataflowOperator for MoveData<'a, 'tcx> {
    #[inline]
    fn initial_value(&self) -> bool {
        false // no loans in scope by default
    }
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
