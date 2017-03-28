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

use syntax::ast::{self, MetaItem};
use syntax_pos::DUMMY_SP;

use rustc::mir::{self, BasicBlock, Mir, Statement, Terminator, Location};
use rustc::session::Session;
use rustc::ty::{self, TyCtxt};
use rustc_mir::util::elaborate_drops::DropFlagState;
use rustc_data_structures::indexed_set::{IdxSetBuf, IdxSet};
use rustc_data_structures::indexed_vec::{Idx};

mod abs_domain;
pub mod elaborate_drops;
mod dataflow;
mod gather_moves;
// mod graphviz;

use self::dataflow::{BitDenotation, BlockSets};
use self::dataflow::{DataflowOperator};
use self::dataflow::{Dataflow, DataflowAnalysis, DataflowResults};
use self::dataflow::{DataflowResultsConsumer};
use self::dataflow::{MaybeInitializedLvals, MaybeUninitializedLvals};
use self::dataflow::{DefinitelyInitializedLvals};
use self::gather_moves::{HasMoveData, MoveData, MovePathIndex, LookupResult};

pub use self::dataflow::{Borrows};
pub(self) use self::gather_moves::{BorrowIndex};

use std::fmt;
use std::mem;

fn has_rustc_mir_with(attrs: &[ast::Attribute], name: &str) -> Option<MetaItem> {
    for attr in attrs {
        if attr.check_name("rustc_mir") {
            let items = attr.meta_item_list();
            for item in items.iter().flat_map(|l| l.iter()) {
                match item.meta_item() {
                    Some(mi) if mi.check_name(name) => return Some(mi.clone()),
                    _ => continue
                }
            }
        }
    }
    return None;
}

pub struct MoveDataParamEnv<'tcx> {
    move_data: MoveData<'tcx>,
    param_env: ty::ParameterEnvironment<'tcx>,
}

pub fn borrowck_mir(bcx: &mut BorrowckCtxt,
                    id: ast::NodeId,
                    attributes: &[ast::Attribute]) {
    let tcx = bcx.tcx;
    let def_id = tcx.hir.local_def_id(id);
    debug!("borrowck_mir({}) UNIMPLEMENTED", tcx.item_path_str(def_id));

    let mir = &tcx.item_mir(def_id);
    let param_env = ty::ParameterEnvironment::for_item(tcx, id);
    let move_data = MoveData::gather_moves(mir, tcx, &param_env);
    let mdpe = MoveDataParamEnv { move_data: move_data, param_env: param_env };

    let flow_borrows =
        do_dataflow(tcx, mir, id, attributes, Borrows::new(tcx, mir),
                    |bd, i| bd.location(i));
    let flow_inits =
        do_dataflow(tcx, mir, id, attributes, MaybeInitializedLvals::new(tcx, mir, &mdpe),
                    |bd, i| &bd.move_data().move_paths[i]);
    let flow_uninits =
        do_dataflow(tcx, mir, id, attributes, MaybeUninitializedLvals::new(tcx, mir, &mdpe),
                    |bd, i| &bd.move_data().move_paths[i]);
    let flow_def_inits =
        do_dataflow(tcx, mir, id, attributes, DefinitelyInitializedLvals::new(tcx, mir, &mdpe),
                    |bd, i| &bd.move_data().move_paths[i]);

    if has_rustc_mir_with(attributes, "rustc_peek_maybe_init").is_some() {
        dataflow::sanity_check_via_rustc_peek(bcx.tcx, mir, id, attributes, &flow_inits);
    }
    if has_rustc_mir_with(attributes, "rustc_peek_maybe_uninit").is_some() {
        dataflow::sanity_check_via_rustc_peek(bcx.tcx, mir, id, attributes, &flow_uninits);
    }
    if has_rustc_mir_with(attributes, "rustc_peek_definite_init").is_some() {
        dataflow::sanity_check_via_rustc_peek(bcx.tcx, mir, id, attributes, &flow_def_inits);
    }

    if has_rustc_mir_with(attributes, "stop_after_dataflow").is_some() {
        bcx.tcx.sess.fatal("stop_after_dataflow ended compilation");
    }

    let mut mbcx = MirBorrowckCtxt {
        bcx: bcx,
        mir: mir,
        node_id: id,
        move_data: &mdpe.move_data,
    };

    let mut state = InProgress {
        borrows: FlowInProgress::new(flow_borrows),
        inits: FlowInProgress::new(flow_inits),
        uninits: FlowInProgress::new(flow_uninits),
    };

    mbcx.analyze_results(&mut state); // entry point for DataflowResultsConsumer

    debug!("borrowck_mir done");
}

fn do_dataflow<'a, 'tcx, BD, P>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                mir: &Mir<'tcx>,
                                node_id: ast::NodeId,
                                attributes: &[ast::Attribute],
                                bd: BD,
                                p: P)
                                -> DataflowResults<BD>
    where BD: BitDenotation + DataflowOperator,
          P: Fn(&BD, BD::Idx) -> &fmt::Debug
{
    let name_found = |sess: &Session, attrs: &[ast::Attribute], name| -> Option<String> {
        if let Some(item) = has_rustc_mir_with(attrs, name) {
            if let Some(s) = item.value_str() {
                return Some(s.to_string())
            } else {
                sess.span_err(
                    item.span,
                    &format!("{} attribute requires a path", item.name()));
                return None;
            }
        }
        return None;
    };

    let print_preflow_to =
        name_found(tcx.sess, attributes, "borrowck_graphviz_preflow");
    let print_postflow_to =
        name_found(tcx.sess, attributes, "borrowck_graphviz_postflow");

    let mut mbcx = MirBorrowckCtxtPreDataflow {
        node_id: node_id,
        print_preflow_to: print_preflow_to,
        print_postflow_to: print_postflow_to,
        flow_state: DataflowAnalysis::new(tcx, mir, bd),
    };

    mbcx.dataflow(p);
    mbcx.flow_state.results()
}

pub struct MirBorrowckCtxtPreDataflow<'a, 'tcx: 'a, BD> where BD: BitDenotation
{
    node_id: ast::NodeId,
    flow_state: DataflowAnalysis<'a, 'tcx, BD>,
    print_preflow_to: Option<String>,
    print_postflow_to: Option<String>,
}

struct FlowInProgress<BD> where BD: BitDenotation {
    base_results: DataflowResults<BD>,
    curr_state: IdxSetBuf<BD::Idx>,
    stmt_gen: IdxSetBuf<BD::Idx>,
    stmt_kill: IdxSetBuf<BD::Idx>,
}

impl<BD> FlowInProgress<BD> where BD: BitDenotation {
    fn each_bit<F>(&self, f: F) where F: FnMut(BD::Idx) {
        each_bit(&self.curr_state, self.base_results.operator().bits_per_block(), f)
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

    fn reconstruct_statement_effect(&mut self, bb: BasicBlock, stmt_idx: usize) {
        self.stmt_gen.reset_to_empty();
        self.stmt_kill.reset_to_empty();
        let mut ignored = IdxSetBuf::new_empty(0);
        let mut sets = BlockSets {
            on_entry: &mut ignored, gen_set: &mut self.stmt_gen, kill_set: &mut self.stmt_kill,
        };
        self.base_results.operator().statement_effect(&mut sets, bb, stmt_idx);
    }

    fn apply_statement_effect(&mut self) {
        self.curr_state.union(&self.stmt_gen);
        self.curr_state.subtract(&self.stmt_kill);
    }
}

#[allow(dead_code)]
pub struct MirBorrowckCtxt<'b, 'a: 'b, 'tcx: 'a> {
    bcx: &'b mut BorrowckCtxt<'a, 'tcx>,
    mir: &'b Mir<'tcx>,
    node_id: ast::NodeId,
    move_data: &'b MoveData<'tcx>,
}

// (forced to be `pub` due to its use as an associated type below.)
pub struct InProgress<'b, 'tcx: 'b> {
    borrows: FlowInProgress<Borrows<'b, 'tcx>>,
    inits: FlowInProgress<MaybeInitializedLvals<'b, 'tcx>>,
    uninits: FlowInProgress<MaybeUninitializedLvals<'b, 'tcx>>,
}

impl<'b, 'tcx: 'b> InProgress<'b, 'tcx> {
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

        s.push_str("borrows: [");
        self.borrows.each_bit(|borrow| {
            let borrow_data = &self.borrows.base_results.operator().borrows()[borrow];
            s.push_str(&format!("{:?}, ", borrow_data));
        });
        s.push_str("] ");

        s.push_str("inits: [");
        self.inits.each_bit(|mpi_init| {
            let move_path =
                &self.inits.base_results.operator().move_data().move_paths[mpi_init];
            s.push_str(&format!("{:?}, ", move_path));
        });
        s.push_str("] ");

        s.push_str("uninits: [");
        self.uninits.each_bit(|mpi_uninit| {
            let move_path =
                &self.uninits.base_results.operator().move_data().move_paths[mpi_uninit];
            s.push_str(&format!("{:?}, ", move_path));
        });
        s.push_str("]");

        return s;
    }
}

fn each_bit<I: Idx, F>(words: &IdxSet<I>, max_bits: usize, mut f: F) where F: FnMut(I) {
    let usize_bits: usize = mem::size_of::<usize>() * 8;

    for (word_index, &word) in words.words().iter().enumerate() {
        if word != 0 {
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
                    // that we are in range of `max_bits`.
                    let bit_index = base_index + offset as usize;
                    if bit_index >= max_bits {
                        return;
                    } else {
                        f(Idx::new(bit_index));
                    }
                }
            }
        }
    }
}

impl<'b, 'a: 'b, 'tcx: 'a> DataflowResultsConsumer<'b, 'tcx> for MirBorrowckCtxt<'b, 'a, 'tcx> {
    type FlowState = InProgress<'b, 'tcx>;

    fn mir(&self) -> &'b Mir<'tcx> { self.mir }

    fn reset_to_entry_of(&mut self, bb: BasicBlock, flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.reset_to_entry_of(bb),
                             |i| i.reset_to_entry_of(bb),
                             |u| u.reset_to_entry_of(bb));
    }

    fn apply_statement_effect(&mut self,
                              bb: BasicBlock,
                              stmt_idx: usize,
                              flow_state: &mut Self::FlowState) {
        flow_state.each_flow(|b| b.reconstruct_statement_effect(bb, stmt_idx),
                             |i| i.reconstruct_statement_effect(bb, stmt_idx),
                             |u| u.reconstruct_statement_effect(bb, stmt_idx));
        flow_state.each_flow(|b| b.apply_statement_effect(),
                             |i| i.apply_statement_effect(),
                             |u| u.apply_statement_effect());
    }

    fn visit_block_entry(&mut self,
                         bb: BasicBlock,
                         flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_block({:?}): {}", bb, summary);
    }

    fn visit_statement_entry(&mut self,
                             bb: BasicBlock,
                             _: usize,
                             stmt: &Statement<'tcx>,
                             flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_statement({:?}, {:?}): {}", bb, stmt, summary);
    }
    fn visit_terminator_entry(&mut self,
                              bb: BasicBlock,
                              _: usize,
                              term: &Terminator<'tcx>,
                              flow_state: &Self::FlowState) {
        let summary = flow_state.summary();
        debug!("MirBorrowckCtxt::process_terminator({:?}, {:?}): {}", bb, term, summary);
    }
}

fn move_path_children_matching<'tcx, F>(move_data: &MoveData<'tcx>,
                                        path: MovePathIndex,
                                        mut cond: F)
                                        -> Option<MovePathIndex>
    where F: FnMut(&mir::LvalueProjection<'tcx>) -> bool
{
    let mut next_child = move_data.move_paths[path].first_child;
    while let Some(child_index) = next_child {
        match move_data.move_paths[child_index].lvalue {
            mir::Lvalue::Projection(ref proj) => {
                if cond(proj) {
                    return Some(child_index)
                }
            }
            _ => {}
        }
        next_child = move_data.move_paths[child_index].next_sibling;
    }

    None
}

/// When enumerating the child fragments of a path, don't recurse into
/// paths (1.) past arrays, slices, and pointers, nor (2.) into a type
/// that implements `Drop`.
///
/// Lvalues behind references or arrays are not tracked by elaboration
/// and are always assumed to be initialized when accessible. As
/// references and indexes can be reseated, trying to track them can
/// only lead to trouble.
///
/// Lvalues behind ADT's with a Drop impl are not tracked by
/// elaboration since they can never have a drop-flag state that
/// differs from that of the parent with the Drop impl.
///
/// In both cases, the contents can only be accessed if and only if
/// their parents are initialized. This implies for example that there
/// is no need to maintain separate drop flags to track such state.
///
/// FIXME: we have to do something for moving slice patterns.
fn lvalue_contents_drop_state_cannot_differ<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                                      mir: &Mir<'tcx>,
                                                      lv: &mir::Lvalue<'tcx>) -> bool {
    let ty = lv.ty(mir, tcx).to_ty(tcx);
    match ty.sty {
        ty::TyArray(..) | ty::TySlice(..) | ty::TyRef(..) | ty::TyRawPtr(..) => {
            debug!("lvalue_contents_drop_state_cannot_differ lv: {:?} ty: {:?} refd => true",
                   lv, ty);
            true
        }
        ty::TyAdt(def, _) if (def.has_dtor(tcx) && !def.is_box()) || def.is_union() => {
            debug!("lvalue_contents_drop_state_cannot_differ lv: {:?} ty: {:?} Drop => true",
                   lv, ty);
            true
        }
        _ => {
            false
        }
    }
}

fn on_lookup_result_bits<'a, 'tcx, F>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &Mir<'tcx>,
    move_data: &MoveData<'tcx>,
    lookup_result: LookupResult,
    each_child: F)
    where F: FnMut(MovePathIndex)
{
    match lookup_result {
        LookupResult::Parent(..) => {
            // access to untracked value - do not touch children
        }
        LookupResult::Exact(e) => {
            on_all_children_bits(tcx, mir, move_data, e, each_child)
        }
    }
}

fn on_all_children_bits<'a, 'tcx, F>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &Mir<'tcx>,
    move_data: &MoveData<'tcx>,
    move_path_index: MovePathIndex,
    mut each_child: F)
    where F: FnMut(MovePathIndex)
{
    fn is_terminal_path<'a, 'tcx>(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        mir: &Mir<'tcx>,
        move_data: &MoveData<'tcx>,
        path: MovePathIndex) -> bool
    {
        lvalue_contents_drop_state_cannot_differ(
            tcx, mir, &move_data.move_paths[path].lvalue)
    }

    fn on_all_children_bits<'a, 'tcx, F>(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        mir: &Mir<'tcx>,
        move_data: &MoveData<'tcx>,
        move_path_index: MovePathIndex,
        each_child: &mut F)
        where F: FnMut(MovePathIndex)
    {
        each_child(move_path_index);

        if is_terminal_path(tcx, mir, move_data, move_path_index) {
            return
        }

        let mut next_child_index = move_data.move_paths[move_path_index].first_child;
        while let Some(child_index) = next_child_index {
            on_all_children_bits(tcx, mir, move_data, child_index, each_child);
            next_child_index = move_data.move_paths[child_index].next_sibling;
        }
    }
    on_all_children_bits(tcx, mir, move_data, move_path_index, &mut each_child);
}

fn drop_flag_effects_for_function_entry<'a, 'tcx, F>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &Mir<'tcx>,
    ctxt: &MoveDataParamEnv<'tcx>,
    mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState)
{
    let move_data = &ctxt.move_data;
    for arg in mir.args_iter() {
        let lvalue = mir::Lvalue::Local(arg);
        let lookup_result = move_data.rev_lookup.find(&lvalue);
        on_lookup_result_bits(tcx, mir, move_data,
                              lookup_result,
                              |moi| callback(moi, DropFlagState::Present));
    }
}

fn drop_flag_effects_for_location<'a, 'tcx, F>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    mir: &Mir<'tcx>,
    ctxt: &MoveDataParamEnv<'tcx>,
    loc: Location,
    mut callback: F)
    where F: FnMut(MovePathIndex, DropFlagState)
{
    let move_data = &ctxt.move_data;
    let param_env = &ctxt.param_env;
    debug!("drop_flag_effects_for_location({:?})", loc);

    // first, move out of the RHS
    for mi in &move_data.loc_map[loc] {
        let path = mi.move_path_index(move_data);
        debug!("moving out of path {:?}", move_data.move_paths[path]);

        // don't move out of non-Copy things
        let lvalue = &move_data.move_paths[path].lvalue;
        let ty = lvalue.ty(mir, tcx).to_ty(tcx);
        if !ty.moves_by_default(tcx, param_env, DUMMY_SP) {
            continue;
        }

        on_all_children_bits(tcx, mir, move_data,
                             path,
                             |moi| callback(moi, DropFlagState::Absent))
    }

    let block = &mir[loc.block];
    match block.statements.get(loc.statement_index) {
        Some(stmt) => match stmt.kind {
            mir::StatementKind::SetDiscriminant{ .. } => {
                span_bug!(stmt.source_info.span, "SetDiscrimant should not exist during borrowck");
            }
            mir::StatementKind::Assign(ref lvalue, _) => {
                debug!("drop_flag_effects: assignment {:?}", stmt);
                 on_lookup_result_bits(tcx, mir, move_data,
                                       move_data.rev_lookup.find(lvalue),
                                       |moi| callback(moi, DropFlagState::Present))
            }
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::InlineAsm { .. } |
            mir::StatementKind::EndRegion(_) |
            mir::StatementKind::Nop => {}
        },
        None => {
            debug!("drop_flag_effects: replace {:?}", block.terminator());
            match block.terminator().kind {
                mir::TerminatorKind::DropAndReplace { ref location, .. } => {
                    on_lookup_result_bits(tcx, mir, move_data,
                                          move_data.rev_lookup.find(location),
                                          |moi| callback(moi, DropFlagState::Present))
                }
                _ => {
                    // other terminators do not contain move-ins
                }
            }
        }
    }
}
