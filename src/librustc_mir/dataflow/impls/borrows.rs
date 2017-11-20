// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::mir::{self, Location, Mir, Lvalue};
use rustc::mir::visit::{LvalueContext, Visitor};
use rustc::ty::{Region, TyCtxt};
use rustc::ty::RegionKind;
use rustc::ty::RegionKind::ReScope;
use rustc::util::nodemap::{FxHashMap, FxHashSet};

use rustc_data_structures::bitslice::{BitwiseOperator};
use rustc_data_structures::indexed_set::{IdxSet};
use rustc_data_structures::indexed_vec::{IndexVec, Idx};

use dataflow::{BitDenotation, BlockSets, DataflowOperator};
pub use dataflow::indexes::{BorrowIndex, BorrowBitIndex};
use transform::nll::region_infer::RegionInferenceContext;
use transform::nll::ToRegionIndex;

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
    assigned_map: FxHashMap<Lvalue<'tcx>, FxHashSet<BorrowIndex>>,
    region_map: FxHashMap<Region<'tcx>, FxHashSet<BorrowIndex>>,
    region_span_map: FxHashMap<RegionKind, Span>,
    nonlexical_regioncx: Option<&'a RegionInferenceContext<'tcx>>,
}

// temporarily allow some dead fields: `kind` and `region` will be
// needed by borrowck; `lvalue` will probably be a MovePathIndex when
// that is extended to include borrowed data paths.
#[allow(dead_code)]
#[derive(Debug)]
pub struct BorrowData<'tcx> {
    pub(crate) location: Location,
    pub(crate) kind: mir::BorrowKind,
    pub(crate) region: Region<'tcx>,
    pub(crate) borrowed_lvalue: mir::Lvalue<'tcx>,
    pub(crate) assigned_lvalue: mir::Lvalue<'tcx>,
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
        write!(w, "&{}{}{:?}", region, kind, self.borrowed_lvalue)
    }
}

impl<'a, 'gcx, 'tcx> Borrows<'a, 'gcx, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'gcx, 'tcx>,
               mir: &'a Mir<'tcx>,
               nonlexical_regioncx: Option<&'a RegionInferenceContext<'tcx>>)
               -> Self {
        let mut visitor = GatherBorrows { idx_vec: IndexVec::new(),
                                          location_map: FxHashMap(),
                                          assigned_map: FxHashMap(),
                                          region_map: FxHashMap(),
                                          region_span_map: FxHashMap()};
        visitor.visit_mir(mir);
        return Borrows { tcx: tcx,
                         mir: mir,
                         borrows: visitor.idx_vec,
                         location_map: visitor.location_map,
                         assigned_map: visitor.assigned_map,
                         region_map: visitor.region_map,
                         region_span_map: visitor.region_span_map,
                         nonlexical_regioncx };

        struct GatherBorrows<'tcx> {
            idx_vec: IndexVec<BorrowIndex, BorrowData<'tcx>>,
            location_map: FxHashMap<Location, BorrowIndex>,
            assigned_map: FxHashMap<Lvalue<'tcx>, FxHashSet<BorrowIndex>>,
            region_map: FxHashMap<Region<'tcx>, FxHashSet<BorrowIndex>>,
            region_span_map: FxHashMap<RegionKind, Span>,
        }
        impl<'tcx> Visitor<'tcx> for GatherBorrows<'tcx> {
            fn visit_assign(&mut self,
                            block: mir::BasicBlock,
                            assigned_lvalue: &mir::Lvalue<'tcx>,
                            rvalue: &mir::Rvalue<'tcx>,
                            location: mir::Location) {
                if let mir::Rvalue::Ref(region, kind, ref borrowed_lvalue) = *rvalue {
                    let borrow = BorrowData {
                        location: location, kind: kind, region: region,
                        borrowed_lvalue: borrowed_lvalue.clone(),
                        assigned_lvalue: assigned_lvalue.clone(),
                    };
                    let idx = self.idx_vec.push(borrow);
                    self.location_map.insert(location, idx);
                    let assigned = find_set_for(&mut self.assigned_map, assigned_lvalue);
                    assigned.insert(idx);
                    let borrows = find_set_for(&mut self.region_map, &region);
                    borrows.insert(idx);
                }
                return self.super_assign(block, assigned_lvalue, rvalue, location);

                fn find_set_for<'a, K, V>(map: &'a mut FxHashMap<K, FxHashSet<V>>,
                                          k: &K)
                                          -> &'a mut FxHashSet<V>
                    where K: Clone+Eq+Hash, V:Eq+Hash
                {
                    map.entry(k.clone()).or_insert(FxHashSet())
                }
            }

            fn visit_rvalue(&mut self,
                            rvalue: &mir::Rvalue<'tcx>,
                            _location: mir::Location) {
                if let mir::Rvalue::Ref(_region, _kind, ref _lvalue) = *rvalue {
                    // TOOD: double-check that we have already registered a BorrowData for this.
                }
            }

            fn visit_statement(&mut self,
                               block: mir::BasicBlock,
                               statement: &mir::Statement<'tcx>,
                               location: Location) {
                if let mir::StatementKind::EndRegion(region_scope) = statement.kind {
                    self.region_span_map.insert(ReScope(region_scope), statement.source_info.span);
                }
                self.super_statement(block, statement, location);
            }
        }
    }

    pub fn borrows(&self) -> &IndexVec<BorrowIndex, BorrowData<'tcx>> { &self.borrows }

    pub fn location(&self, idx: BorrowIndex) -> &Location {
        &self.borrows[idx].location
    }

    /// Returns the span for the "end point" given region. This will
    /// return `None` if NLL is enabled, since that concept has no
    /// meaning there.  Otherwise, return region span if it exists and
    /// span for end of the function if it doesn't exist.
    pub fn opt_region_end_span(&self, region: &Region) -> Option<Span> {
        match self.nonlexical_regioncx {
            Some(_) => None,
            None => {
                match self.region_span_map.get(region) {
                    Some(span) => Some(span.end_point()),
                    None => Some(self.mir.span.end_point())
                }
            }
        }
    }

    /// Add all borrows to the kill set, if those borrows are out of scope at `location`.
    fn kill_loans_out_of_scope_at_location(&self,
                                           sets: &mut BlockSets<BorrowBitIndex>,
                                           location: Location) {
        if let Some(regioncx) = self.nonlexical_regioncx {
            for (borrow_index, borrow_data) in self.borrows.iter_enumerated() {
                let borrow_region = borrow_data.region.to_region_index();
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
                        sets.kill(&borrow_index.reservation());
                        sets.kill(&borrow_index.activation());
                    }
                }
            }
        }
    }
}

/// The `BitDenotation` here is a little unusual: it reserves
/// *two* bits for each index, not just one.
///
/// We have two bits per-index to represent two-phase `&mut` borrows:
/// There is the reservation-state (which starts at the point of a
/// `&mut`-borrow) and the active state (which starts at the first
/// *use* in the control-flow).
///
/// For each index I, the reservation state is at 2*I, and the active
/// state is at 2*I+1.
impl BorrowIndex {
    fn reservation(&self) -> BorrowBitIndex {
        BorrowBitIndex::new(self.index() * 2)
    }
    fn activation(&self) -> BorrowBitIndex {
        BorrowBitIndex::new(self.index() * 2 + 1)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub(crate) enum BorrowPhase { Reservation, Activation }

impl BorrowBitIndex {
    pub(crate) fn origin(&self) -> (BorrowIndex, BorrowPhase) {
        (BorrowIndex::new(self.index() / 2), self.phase())
    }

    pub(crate) fn phase(&self) -> BorrowPhase {
        match self.index() % 2 {
            0 => BorrowPhase::Reservation,
            _ => BorrowPhase::Activation,
        }
    }
}

impl<'a, 'gcx, 'tcx> BitDenotation for Borrows<'a, 'gcx, 'tcx> {
    type Idx = BorrowBitIndex;
    fn name() -> &'static str { "borrows" }
    fn bits_per_block(&self) -> usize {
        self.borrows.len() * 2
    }
    fn start_block_effect(&self, _sets: &mut BlockSets<BorrowBitIndex>)  {
        // no borrows of code region_scopes have been taken prior to
        // function execution, so this method has no effect on
        // `_sets`.
    }
    fn statement_effect(&self,
                        sets: &mut BlockSets<BorrowBitIndex>,
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
                    for idx in borrow_indexes {
                        sets.kill(&idx.reservation());
                        sets.kill(&idx.activation());
                    }
                } else {
                    // (if there is no entry, then there are no borrows to be tracked)
                }
            }

            mir::StatementKind::Assign(_, ref rhs) => {
                if let mir::Rvalue::Ref(region, _, _) = *rhs {
                    let index = self.location_map.get(&location).unwrap_or_else(|| {
                        panic!("could not find BorrowIndex for location {:?}", location);
                    });
                    assert!(self.region_map.get(region).unwrap_or_else(|| {
                        panic!("could not find BorrowIndexs for region {:?}", region);
                    }).contains(&index));
                    sets.gen(&index.reservation());
                    sets.kill(&index.activation());
                }
            }

            mir::StatementKind::InlineAsm { .. } |
            mir::StatementKind::SetDiscriminant { .. } |
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::Validate(..) |
            mir::StatementKind::Nop => {}
        }

        FindLvalueUses { borrows: self, sets }.visit_statement(location.block, stmt, location);

        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<BorrowBitIndex>,
                         location: Location) {
        let block = &self.mir[location.block];
        let term = block.terminator();
        FindLvalueUses { borrows: self, sets }.visit_terminator(location.block, term, location);

        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<BorrowBitIndex>,
                             _call_bb: mir::BasicBlock,
                             _dest_bb: mir::BasicBlock,
                             _dest_lval: &mir::Lvalue) {
        // there are no effects on the region scopes from method calls.
    }
}

struct FindLvalueUses<'b: 'a, 'a, 'gcx: 'tcx, 'tcx: 'a> {
    borrows: &'a Borrows<'a, 'gcx, 'tcx>,
    sets: &'a mut BlockSets<'b, BorrowBitIndex>,
}

impl<'b, 'a, 'gcx, 'tcx> Visitor<'tcx> for FindLvalueUses<'b, 'a, 'gcx, 'tcx> {
    fn visit_lvalue(&mut self,
                    lvalue: &mir::Lvalue<'tcx>,
                    context: LvalueContext<'tcx>,
                    location: Location) {
        match context {
            // pure overwrites of an lvalue do not activate it
            LvalueContext::Store |
            LvalueContext::Call => { }

            // storage effects on an lvalue do not activate it
            LvalueContext::StorageLive |
            LvalueContext::StorageDead => { }

            // reads of an lvalue *do* activate it
            LvalueContext::Drop |
            LvalueContext::Inspect |
            LvalueContext::Borrow { .. } |
            LvalueContext::Projection(..) |
            LvalueContext::Consume |
            LvalueContext::Validate => {
                if let Some(borrows) = self.borrows.assigned_map.get(lvalue) {
                    for borrow_idx in borrows {
                        self.sets.gen(&borrow_idx.activation());
                    }
                }
            }
        }

        self.super_lvalue(lvalue, context, location);
    }
}

impl<'a, 'gcx, 'tcx> BitwiseOperator for Borrows<'a, 'gcx, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // union effects of preds when computing borrows
    }
}

impl<'a, 'gcx, 'tcx> DataflowOperator for Borrows<'a, 'gcx, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = no Rvalue::Refs are active by default
    }
}
