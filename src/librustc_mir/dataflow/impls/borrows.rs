// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::mir::{self, Location, Place, Mir};
use rustc::mir::visit::{PlaceContext, Visitor};
use rustc::ty::{self, Region, TyCtxt};
use rustc::ty::RegionKind;
use rustc::ty::RegionKind::ReScope;
use rustc::util::nodemap::{FxHashMap, FxHashSet};

use rustc_data_structures::bitslice::{BitwiseOperator};
use rustc_data_structures::indexed_set::{IdxSet};
use rustc_data_structures::indexed_vec::{Idx, IndexVec};

use dataflow::{BitDenotation, BlockSets, InitialFlow};
pub use dataflow::indexes::{BorrowIndex, ResActIndex};
use borrow_check::nll::region_infer::RegionInferenceContext;
use borrow_check::nll::ToRegionVid;

use syntax_pos::Span;

use std::fmt;
use std::hash::Hash;

// `Borrows` maps each dataflow bit to an `Rvalue::Ref`, which can be
// uniquely identified in the MIR by the `Location` of the assigment
// statement in which it appears on the right hand side.
pub struct Borrows<'a, 'gcx: 'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    borrows: IndexVec<BorrowIndex, BorrowData<'tcx>>,
    location_map: FxHashMap<Location, BorrowIndex>,
    assigned_map: FxHashMap<Place<'tcx>, FxHashSet<BorrowIndex>>,
    region_map: FxHashMap<Region<'tcx>, FxHashSet<BorrowIndex>>,
    region_span_map: FxHashMap<RegionKind, Span>,
    nonlexical_regioncx: Option<RegionInferenceContext<'tcx>>,
}

pub(crate) struct Reservations<'a, 'gcx: 'tcx, 'tcx: 'a>(Borrows<'a, 'gcx, 'tcx>);
pub(crate) struct ActiveBorrows<'a, 'gcx: 'tcx, 'tcx: 'a>(Borrows<'a, 'gcx, 'tcx>);

impl<'a, 'gcx, 'tcx> Reservations<'a, 'gcx, 'tcx> {
    pub(crate) fn new(b: Borrows<'a, 'gcx, 'tcx>) -> Self { Reservations(b) }
    pub(crate) fn location(&self, idx: ResActIndex) -> &Location {
        self.0.location(idx.borrow_index())
    }
}

impl<'a, 'gcx, 'tcx> ActiveBorrows<'a, 'gcx, 'tcx> {
    pub(crate) fn new(r: Reservations<'a, 'gcx, 'tcx>) -> Self { ActiveBorrows(r.0) }
    pub(crate) fn location(&self, idx: ResActIndex) -> &Location {
        self.0.location(idx.borrow_index())
    }
}

// temporarily allow some dead fields: `kind` and `region` will be
// needed by borrowck; `borrowed_place` will probably be a MovePathIndex when
// that is extended to include borrowed data paths.
#[allow(dead_code)]
#[derive(Debug)]
pub struct BorrowData<'tcx> {
    pub(crate) location: Location,
    pub(crate) kind: mir::BorrowKind,
    pub(crate) region: Region<'tcx>,
    pub(crate) borrowed_place: mir::Place<'tcx>,
    pub(crate) assigned_place: mir::Place<'tcx>,
}

impl<'tcx> fmt::Display for BorrowData<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        let kind = match self.kind {
            mir::BorrowKind::Shared => "",
            mir::BorrowKind::Unique => "uniq ",
            mir::BorrowKind::Mut => "mut ",
        };
        let region = format!("{}", self.region);
        let region = if region.len() > 0 { format!("{} ", region) } else { region };
        write!(w, "&{}{}{:?}", region, kind, self.borrowed_place)
    }
}

impl ResActIndex {
    fn reserved(i: BorrowIndex) -> Self { ResActIndex::new((i.index() * 2)) }
    fn active(i: BorrowIndex) -> Self { ResActIndex::new((i.index() * 2) + 1) }

    pub(crate) fn is_reservation(self) -> bool { self.index() % 2 == 0 }
    pub(crate) fn is_activation(self) -> bool { self.index() % 2 == 1}

    pub(crate) fn kind(self) -> &'static str {
        if self.is_reservation() { "reserved" } else { "active" }
    }
    pub(crate) fn borrow_index(self) -> BorrowIndex {
        BorrowIndex::new(self.index() / 2)
    }
}

impl<'a, 'gcx, 'tcx> Borrows<'a, 'gcx, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'gcx, 'tcx>,
               mir: &'a Mir<'tcx>,
               nonlexical_regioncx: Option<RegionInferenceContext<'tcx>>)
               -> Self {
        let mut visitor = GatherBorrows {
            tcx,
            mir,
            idx_vec: IndexVec::new(),
            location_map: FxHashMap(),
            assigned_map: FxHashMap(),
            region_map: FxHashMap(),
            region_span_map: FxHashMap()
        };
        visitor.visit_mir(mir);
        return Borrows { tcx: tcx,
                         mir: mir,
                         borrows: visitor.idx_vec,
                         location_map: visitor.location_map,
                         assigned_map: visitor.assigned_map,
                         region_map: visitor.region_map,
                         region_span_map: visitor.region_span_map,
                         nonlexical_regioncx };

        struct GatherBorrows<'a, 'gcx: 'tcx, 'tcx: 'a> {
            tcx: TyCtxt<'a, 'gcx, 'tcx>,
            mir: &'a Mir<'tcx>,
            idx_vec: IndexVec<BorrowIndex, BorrowData<'tcx>>,
            location_map: FxHashMap<Location, BorrowIndex>,
            assigned_map: FxHashMap<Place<'tcx>, FxHashSet<BorrowIndex>>,
            region_map: FxHashMap<Region<'tcx>, FxHashSet<BorrowIndex>>,
            region_span_map: FxHashMap<RegionKind, Span>,
        }

        impl<'a, 'gcx, 'tcx> Visitor<'tcx> for GatherBorrows<'a, 'gcx, 'tcx> {
            fn visit_assign(&mut self,
                            block: mir::BasicBlock,
                            assigned_place: &mir::Place<'tcx>,
                            rvalue: &mir::Rvalue<'tcx>,
                            location: mir::Location) {
                if let mir::Rvalue::Ref(region, kind, ref borrowed_place) = *rvalue {
                    if is_unsafe_place(self.tcx, self.mir, borrowed_place) { return; }

                    let borrow = BorrowData {
                        location, kind, region,
                        borrowed_place: borrowed_place.clone(),
                        assigned_place: assigned_place.clone(),
                    };
                    let idx = self.idx_vec.push(borrow);
                    self.location_map.insert(location, idx);
                    find_set_for(&mut self.assigned_map, assigned_place).insert(idx);
                    find_set_for(&mut self.region_map, &region).insert(idx);
                }

                return self.super_assign(block, assigned_place, rvalue, location);

                fn find_set_for<'a, K, V>(map: &'a mut FxHashMap<K, FxHashSet<V>>,
                                          k: &K)
                                          -> &'a mut FxHashSet<V>
                    where K: Clone+Eq+Hash, V: Eq+Hash
                {
                    map.entry(k.clone()).or_insert(FxHashSet())
                }
            }

            fn visit_rvalue(&mut self,
                            rvalue: &mir::Rvalue<'tcx>,
                            location: mir::Location) {
                if let mir::Rvalue::Ref(region, kind, ref place) = *rvalue {
                    // double-check that we already registered a BorrowData for this

                    let mut found_it = false;
                    for idx in &self.region_map[region] {
                        let bd = &self.idx_vec[*idx];
                        if bd.location == location &&
                            bd.kind == kind &&
                            bd.region == region &&
                            bd.borrowed_place == *place
                        {
                            found_it = true;
                            break;
                        }
                    }
                    assert!(found_it, "Ref {:?} at {:?} missing BorrowData", rvalue, location);
                }

                return self.super_rvalue(rvalue, location);
            }

            fn visit_statement(&mut self,
                               block: mir::BasicBlock,
                               statement: &mir::Statement<'tcx>,
                               location: Location) {
                if let mir::StatementKind::EndRegion(region_scope) = statement.kind {
                    self.region_span_map.insert(ReScope(region_scope), statement.source_info.span);
                }
                return self.super_statement(block, statement, location);
            }
        }
    }

    pub fn borrows(&self) -> &IndexVec<BorrowIndex, BorrowData<'tcx>> { &self.borrows }

    pub fn location(&self, idx: BorrowIndex) -> &Location {
        &self.borrows[idx].location
    }

    /// Add all borrows to the kill set, if those borrows are out of scope at `location`.
    fn kill_loans_out_of_scope_at_location(&self,
                                           sets: &mut BlockSets<ResActIndex>,
                                           location: Location) {
        if let Some(ref regioncx) = self.nonlexical_regioncx {
            for (borrow_index, borrow_data) in self.borrows.iter_enumerated() {
                let borrow_region = borrow_data.region.to_region_vid();
                if !regioncx.region_contains_point(borrow_region, location) {
                    // The region checker really considers the borrow
                    // to start at the point **after** the location of
                    // the borrow, but the borrow checker puts the gen
                    // directly **on** the location of the
                    // borrow. This results in a gen/kill both being
                    // generated for same point if we are not
                    // careful. Probably we should change the point of
                    // the gen, but for now we hackily account for the
                    // mismatch here by not generating a kill for the
                    // location on the borrow itself.
                    if location != borrow_data.location {
                        sets.kill(&ResActIndex::reserved(borrow_index));
                        sets.kill(&ResActIndex::active(borrow_index));
                    }
                }
            }
        }
    }

    fn statement_effect_on_reservations(&self,
                                        sets: &mut BlockSets<ResActIndex>,
                                        location: Location) {
        let block = &self.mir.basic_blocks().get(location.block).unwrap_or_else(|| {
            panic!("could not find block at location {:?}", location);
        });
        let stmt = block.statements.get(location.statement_index).unwrap_or_else(|| {
            panic!("could not find statement at location {:?}");
        });
        match stmt.kind {
            mir::StatementKind::EndRegion(region_scope) => {
                if let Some(borrow_indexes) = self.region_map.get(&ReScope(region_scope)) {
                    assert!(self.nonlexical_regioncx.is_none());
                    for idx in borrow_indexes { sets.kill(&ResActIndex::reserved(*idx)); }
                } else {
                    // (if there is no entry, then there are no borrows to be tracked)
                }
            }

            mir::StatementKind::Assign(_, ref rhs) => {
                if let mir::Rvalue::Ref(region, _, ref place) = *rhs {
                    if is_unsafe_place(self.tcx, self.mir, place) { return; }
                    if let RegionKind::ReEmpty = region {
                        // If the borrowed value is dead, the region for it
                        // can be empty. Don't track the borrow in that case.
                        return
                    }

                    let index = self.location_map.get(&location).unwrap_or_else(|| {
                        panic!("could not find BorrowIndex for location {:?}", location);
                    });
                    assert!(self.region_map.get(region).unwrap_or_else(|| {
                        panic!("could not find BorrowIndexs for region {:?}", region);
                    }).contains(&index));
                    sets.gen(&ResActIndex::reserved(*index));
                }
            }

            mir::StatementKind::InlineAsm { .. } |
            mir::StatementKind::SetDiscriminant { .. } |
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Validate(..) |
            mir::StatementKind::Nop => {}

        }

        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn statement_effect_on_activations(&self,
                                       sets: &mut BlockSets<ResActIndex>,
                                       location: Location) {
        let block = &self.mir.basic_blocks().get(location.block).unwrap_or_else(|| {
            panic!("could not find block at location {:?}", location);
        });
        let stmt = block.statements.get(location.statement_index).unwrap_or_else(|| {
            panic!("could not find statement at location {:?}");
        });

        // INVARIANT: At this point, sets.on_entry should correctly
        // reflect the reservations as we enter the statement.

        // Now compute the effect of the statement on the activations
        // themselves in the ActiveBorrows state.

        // First: Any uses of reserved Lvalues in the statement are now activated.
        {
            let mut find = FindPlaceUses { sets, assigned_map: &self.assigned_map };
            find.visit_statement(location.block, stmt, location);
        }

        // Second: EndRegion kills any active borrows.
        match stmt.kind {
            mir::StatementKind::EndRegion(region_scope) => {
                if let Some(borrow_indexes) = self.region_map.get(&ReScope(region_scope)) {
                    assert!(self.nonlexical_regioncx.is_none());
                    for idx in borrow_indexes { sets.kill(&ResActIndex::active(*idx)); }
                } else {
                    // (if there is no entry, then there are no borrows to be tracked)
                }
            }

            mir::StatementKind::Assign(..) |
            mir::StatementKind::InlineAsm { .. } |
            mir::StatementKind::SetDiscriminant { .. } |
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Validate(..) |
            mir::StatementKind::Nop => {}
        }

        // Now we have finished computing the effect of the statement
        // on the activations.
        //
        // But before we return, we need to establish the statement's
        // effect on the reservations, in order to re-establish the
        // INVARIANT noted above.
        //
        // (Note that we put this after the computation of
        // activation-effects because that *reads* the reservation
        // state on entry.).

        self.statement_effect_on_reservations(sets, location);
    }

    fn terminator_effect_on_reservations(&self,
                                         sets: &mut BlockSets<ResActIndex>,
                                         location: Location) {
        let block = &self.mir.basic_blocks().get(location.block).unwrap_or_else(|| {
            panic!("could not find block at location {:?}", location);
        });
        match block.terminator().kind {
            mir::TerminatorKind::Resume |
            mir::TerminatorKind::Return |
            mir::TerminatorKind::GeneratorDrop => {
                // When we return from the function, then all `ReScope`-style regions
                // are guaranteed to have ended.
                // Normally, there would be `EndRegion` statements that come before,
                // and hence most of these loans will already be dead -- but, in some cases
                // like unwind paths, we do not always emit `EndRegion` statements, so we
                // add some kills here as a "backup" and to avoid spurious error messages.
                for (borrow_index, borrow_data) in self.borrows.iter_enumerated() {
                    if let ReScope(..) = borrow_data.region {
                        sets.kill(&ResActIndex::reserved(borrow_index));
                    }
                }
            }
            mir::TerminatorKind::SwitchInt {..} |
            mir::TerminatorKind::Drop {..} |
            mir::TerminatorKind::DropAndReplace {..} |
            mir::TerminatorKind::Call {..} |
            mir::TerminatorKind::Assert {..} |
            mir::TerminatorKind::Yield {..} |
            mir::TerminatorKind::Goto {..} |
            mir::TerminatorKind::FalseEdges {..} |
            mir::TerminatorKind::Unreachable => {}
        }
        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn terminator_effect_on_activations(&self,
                                        sets: &mut BlockSets<ResActIndex>,
                                        location: Location) {
        let block = &self.mir[location.block];
        let term = block.terminator();
        // Any uses of reserved Lvalues in the statement are now activated.
        {
            let mut find = FindPlaceUses { sets, assigned_map: &self.assigned_map };
            find.visit_terminator(location.block, term, location);
        }

        match block.terminator().kind {
            mir::TerminatorKind::Resume |
            mir::TerminatorKind::Return |
            mir::TerminatorKind::GeneratorDrop => {
                // When we return from the function, then all `ReScope`-style regions
                // are guaranteed to have ended.
                // Normally, there would be `EndRegion` statements that come before,
                // and hence most of these loans will already be dead -- but, in some cases
                // like unwind paths, we do not always emit `EndRegion` statements, so we
                // add some kills here as a "backup" and to avoid spurious error messages.
                for (borrow_index, borrow_data) in self.borrows.iter_enumerated() {
                    if let ReScope(..) = borrow_data.region {
                        sets.kill(&ResActIndex::active(borrow_index));
                    }
                }
            }
            mir::TerminatorKind::SwitchInt {..} |
            mir::TerminatorKind::Drop {..} |
            mir::TerminatorKind::DropAndReplace {..} |
            mir::TerminatorKind::Call {..} |
            mir::TerminatorKind::Assert {..} |
            mir::TerminatorKind::Yield {..} |
            mir::TerminatorKind::Goto {..} |
            mir::TerminatorKind::FalseEdges {..} |
            mir::TerminatorKind::Unreachable => {}
        }

        // Now we have finished computing the effect of the terminator
        // on the activations.
        //
        // But before we return, we need to establish the terminator's
        // effect on the reservations. (borrow_check relies on the
        // reservation state represented alongside the activations in
        // the ActiveBorrows, even at the end of basic blocks.)
        self.terminator_effect_on_reservations(sets, location);
    }
}

impl<'a, 'gcx, 'tcx> ActiveBorrows<'a, 'gcx, 'tcx> {
    pub(crate) fn borrows(&self) -> &IndexVec<BorrowIndex, BorrowData<'tcx>> {
        self.0.borrows()
    }

    /// Returns the span for the "end point" given region. This will
    /// return `None` if NLL is enabled, since that concept has no
    /// meaning there.  Otherwise, return region span if it exists and
    /// span for end of the function if it doesn't exist.
    pub(crate) fn opt_region_end_span(&self, region: &Region) -> Option<Span> {
        match self.0.nonlexical_regioncx {
            Some(_) => None,
            None => {
                match self.0.region_span_map.get(region) {
                    Some(span) => Some(span.end_point()),
                    None => Some(self.0.mir.span.end_point())
                }
            }
        }
    }
}

struct FindPlaceUses<'a, 'b: 'a, 'tcx: 'a> {
    assigned_map: &'a FxHashMap<Place<'tcx>, FxHashSet<BorrowIndex>>,
    sets: &'a mut BlockSets<'b, ResActIndex>,
}

impl<'a, 'b, 'tcx> FindPlaceUses<'a, 'b, 'tcx> {
    fn has_been_reserved(&self, b: &BorrowIndex) -> bool {
        self.sets.on_entry.contains(&ResActIndex::reserved(*b))
    }

    fn is_potential_use(context: PlaceContext) -> bool {
        match context {
            // storage effects on an place do not activate it
            PlaceContext::StorageLive | PlaceContext::StorageDead => false,

            // validation effects do not activate an place
            //
            // FIXME: Should they? Is it just another read? Or can we
            // guarantee it won't dereference the stored address? How
            // "deep" does validation go?
            PlaceContext::Validate => false,

            // pure overwrites of an lvalue do not activate it. (note
            // LvalueContext::Call is solely about dest lvalue)
            PlaceContext::Store | PlaceContext::Call => false,

            // reads of an lvalue *do* activate it
            PlaceContext::Move |
            PlaceContext::Copy |
            PlaceContext::Drop |
            PlaceContext::Inspect |
            PlaceContext::Borrow { .. } |
            PlaceContext::Projection(..) => true,
        }
    }
}

impl<'a, 'b, 'tcx> Visitor<'tcx> for FindPlaceUses<'a, 'b, 'tcx> {
    fn visit_place(&mut self,
                    place: &mir::Place<'tcx>,
                    context: PlaceContext<'tcx>,
                    location: Location) {
        debug!("FindPlaceUses place: {:?} assigned from borrows: {:?} \
                used in context: {:?} at location: {:?}",
               place, self.assigned_map.get(place), context, location);
        if Self::is_potential_use(context) {
            if let Some(borrows) = self.assigned_map.get(place) {
                for borrow_idx in borrows {
                    debug!("checking if index {:?} for {:?} is reserved ({}) \
                            and thus needs active gen-bit set in sets {:?}",
                           borrow_idx, place, self.has_been_reserved(&borrow_idx), self.sets);
                    if self.has_been_reserved(&borrow_idx) {
                        self.sets.gen(&ResActIndex::active(*borrow_idx));
                    } else {
                        // (This can certainly happen in valid code. I
                        // just want to know about it in the short
                        // term.)
                        info!("encountered use of Place {:?} of borrow_idx {:?} \
                               at location {:?} outside of reservation",
                              place, borrow_idx, location);
                    }
                }
            }
        }

        self.super_place(place, context, location);
    }
}


impl<'a, 'gcx, 'tcx> BitDenotation for Reservations<'a, 'gcx, 'tcx> {
    type Idx = ResActIndex;
    fn name() -> &'static str { "reservations" }
    fn bits_per_block(&self) -> usize {
        self.0.borrows.len() * 2
    }
    fn start_block_effect(&self, _sets: &mut BlockSets<ResActIndex>)  {
        // no borrows of code region_scopes have been taken prior to
        // function execution, so this method has no effect on
        // `_sets`.
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<ResActIndex>,
                        location: Location) {
        debug!("Reservations::statement_effect sets: {:?} location: {:?}", sets, location);
        self.0.statement_effect_on_reservations(sets, location);
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<ResActIndex>,
                         location: Location) {
        debug!("Reservations::terminator_effect sets: {:?} location: {:?}", sets, location);
        self.0.terminator_effect_on_reservations(sets, location);
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<ResActIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             _dest_place: &mir::Place) {
        // there are no effects on the region scopes from method calls.
    }
}

impl<'a, 'gcx, 'tcx> BitDenotation for ActiveBorrows<'a, 'gcx, 'tcx> {
    type Idx = ResActIndex;
    fn name() -> &'static str { "active_borrows" }

    /// Overriding this method; `ActiveBorrows` uses the intrablock
    /// state in `on_entry` to track the current reservations (which
    /// then affect the construction of the gen/kill sets for
    /// activations).
    fn accumulates_intrablock_state() -> bool { true }

    fn bits_per_block(&self) -> usize {
        self.0.borrows.len() * 2
    }

    fn start_block_effect(&self, _sets: &mut BlockSets<ResActIndex>)  {
        // no borrows of code region_scopes have been taken prior to
        // function execution, so this method has no effect on
        // `_sets`.
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<ResActIndex>,
                        location: Location) {
        debug!("ActiveBorrows::statement_effect sets: {:?} location: {:?}", sets, location);
        self.0.statement_effect_on_activations(sets, location);
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<ResActIndex>,
                         location: Location) {
        debug!("ActiveBorrows::terminator_effect sets: {:?} location: {:?}", sets, location);
        self.0.terminator_effect_on_activations(sets, location);
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<ResActIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             _dest_lval: &mir::Place) {
        // there are no effects on activations from method call return
    }
}

impl<'a, 'gcx, 'tcx> BitwiseOperator for Reservations<'a, 'gcx, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // union effects of preds when computing reservations
    }
}

impl<'a, 'gcx, 'tcx> BitwiseOperator for ActiveBorrows<'a, 'gcx, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // union effects of preds when computing activations
    }
}

impl<'a, 'gcx, 'tcx> InitialFlow for Reservations<'a, 'gcx, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = no Rvalue::Refs are reserved by default
    }
}

fn is_unsafe_place<'a, 'gcx: 'tcx, 'tcx: 'a>(
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    place: &mir::Place<'tcx>
) -> bool {
    use self::mir::Place::*;
    use self::mir::ProjectionElem;

    match *place {
        Local(_) => false,
        Static(ref static_) => tcx.is_static_mut(static_.def_id),
        Projection(ref proj) => {
            match proj.elem {
                ProjectionElem::Field(..) |
                ProjectionElem::Downcast(..) |
                ProjectionElem::Subslice { .. } |
                ProjectionElem::ConstantIndex { .. } |
                ProjectionElem::Index(_) => {
                    is_unsafe_place(tcx, mir, &proj.base)
                }
                ProjectionElem::Deref => {
                    let ty = proj.base.ty(mir, tcx).to_ty(tcx);
                    match ty.sty {
                        ty::TyRawPtr(..) => true,
                        _ => is_unsafe_place(tcx, mir, &proj.base),
                    }
                }
            }
        }
    }
}
