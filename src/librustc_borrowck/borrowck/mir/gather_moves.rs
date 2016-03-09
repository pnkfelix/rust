// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use rustc::middle::ty::{self, Ty};
use rustc::middle::def_id::DefId;
use rustc::mir::repr::{self, Mir, BasicBlock, Lvalue, Rvalue};
use rustc::mir::repr::{Operand, ProjectionElem};
use rustc::mir::repr::{StatementKind, Terminator};
use rustc::mir::tcx::{LvalueTy};
use rustc::util::nodemap::FnvHashMap;

use super::dataflow::BitDenotation;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use std::iter;
use std::mem;
use std::ops::Deref;
use std::ops::Index;
use std::usize;

pub use self::abs_domain::*;

/// The move-analysis portion of borrowck needs to work in an abstract
/// domain of lifted Lvalues.  Most of the Lvalue variants fall into a
/// one-to-one mapping between the concrete and abstract (e.g. a
/// field-deref on a local-variable, `x.field`, has the same meaning
/// in both domains). Indexed-Projections are the exception: `a[x]`
/// needs to be treated as mapping to the same move path as `a[y]` as
/// well as `a[13]`, et cetera.
///
/// (In theory the analysis could be extended to work with sets of
/// paths, so that `a[0]` and `a[13]` could be kept distinct, while
/// `a[x]` would still overlap them both. But that is not this
/// representation does today.)
pub mod abs_domain {
    use rustc::mir::repr::{self, Lvalue, LvalueElem};
    use rustc::mir::repr::{Operand, Projection, ProjectionElem};
    #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
    pub struct AbstractOperand;
    pub type AbstractProjection<'tcx> =
        Projection<'tcx, Lvalue<'tcx>, AbstractOperand>;
    pub type AbstractElem<'tcx> =
        ProjectionElem<'tcx, AbstractOperand>;

    pub trait Lift {
        type Abstract;
        fn lift(&self) -> Self::Abstract;
    }
    impl<'tcx> Lift for Operand<'tcx> {
        type Abstract = AbstractOperand;
        fn lift(&self) -> Self::Abstract { AbstractOperand }
    }
    impl<'tcx> Lift for LvalueElem<'tcx> {
        type Abstract = AbstractElem<'tcx>;
        fn lift(&self) -> Self::Abstract {
            match *self {
                ProjectionElem::Deref =>
                    ProjectionElem::Deref,
                ProjectionElem::Field(ref f, ty) =>
                    ProjectionElem::Field(f.clone(), ty.clone()),
                ProjectionElem::Index(ref i) =>
                    ProjectionElem::Index(i.lift()),
                ProjectionElem::ConstantIndex {offset,min_length,from_end} =>
                    ProjectionElem::ConstantIndex {
                        offset: offset,
                        min_length: min_length,
                        from_end: from_end
                    },
                ProjectionElem::Downcast(a, u) =>
                    ProjectionElem::Downcast(a.clone(), u.clone()),
            }
        }
    }
}

/// Index into MovePathData.move_paths
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MovePathIndex(usize);

const INVALID_MOVE_PATH_INDEX: MovePathIndex = MovePathIndex(usize::MAX);

impl MovePathIndex {
    pub fn idx(&self) -> Option<usize> {
        if *self == INVALID_MOVE_PATH_INDEX {
            None
        } else {
            Some(self.0)
        }
    }
}

/// `MovePath` is a canonicalized representation of a path that is
/// moved or assigned to.
///
/// It follows a tree structure.
///
/// Given `struct X { m: M, n: N }` and `x: X`, moves like `drop x.m;`
/// move *out* of the l-value `x.m`.
///
/// The MovePaths representing `x.m` and `x.n` are siblings (that is,
/// one of them will link to the other via the `next_sibling` field,
/// and the other will have no entry in its `next_sibling` field), and
/// they both have the MovePath representing `x` as their parent.
#[derive(Clone)]
pub struct MovePath<'tcx> {
    pub next_sibling: MovePathIndex,
    pub first_child: MovePathIndex,
    pub parent: MovePathIndex,
    pub lvalue: Lvalue<'tcx>,
}

/// During construction of the MovePath's, we use PreMovePath to
/// represent accumulated state while we are gathering up all the
/// children of each path.
#[derive(Clone)]
struct PreMovePath<'tcx> {
    pub next_sibling: MovePathIndex,
    pub first_child: Cell<MovePathIndex>,
    pub parent: MovePathIndex,
    pub lvalue: Lvalue<'tcx>,
}

impl<'tcx> PreMovePath<'tcx> {
    fn into_move_path(self) -> MovePath<'tcx> {
        MovePath {
            next_sibling: self.next_sibling,
            parent: self.parent,
            lvalue: self.lvalue,
            first_child: self.first_child.get(),
        }
    }
}

impl<'tcx> fmt::Debug for MovePath<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(w, "MovePath {{"));
        if self.parent != INVALID_MOVE_PATH_INDEX {
            try!(write!(w, " parent: {:?},", self.parent));
        }
        if self.first_child != INVALID_MOVE_PATH_INDEX {
            try!(write!(w, " first_child: {:?},", self.first_child));
        }
        if self.next_sibling != INVALID_MOVE_PATH_INDEX {
            try!(write!(w, " next_sibling: {:?}", self.next_sibling));
        }
        write!(w, " lvalue: {:?} }}", self.lvalue)
    }
}

/// Index into MoveData.moves.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MoveOutIndex(usize);

impl MoveOutIndex {
    pub fn idx(&self) -> Option<usize> {
        if *self == INVALID_MOVE_OUT_INDEX {
            None
        } else {
            Some(self.0)
        }
    }
}

const INVALID_MOVE_OUT_INDEX: MoveOutIndex = MoveOutIndex(usize::MAX);

pub struct MoveData<'a, 'tcx:'a> {
    pub move_paths: MovePathData<'a, 'tcx>,
    pub moves: Vec<MoveOut>,
    pub loc_map: LocMap,
    pub path_map: PathMap,
    pub rev_lookup: MovePathLookup<'tcx>,
}

pub struct LocMap {
    // Location-indexed (BasicBlock for outer index, index within BB
    // for inner index) map to list of MoveOutIndex's.
    map: Vec<Vec<Vec<MoveOutIndex>>>,
}

impl Index<Location> for LocMap {
    type Output = [MoveOutIndex];
    fn index(&self, index: Location) -> &Self::Output {
        assert!(index.block.index() < self.map.len());
        assert!(index.index < self.map[index.block.index()].len());
        &self.map[index.block.index()][index.index]
    }
}

pub struct PathMap {
    // Path-indexed map to list of MoveOutIndex's.
    map: Vec<Vec<MoveOutIndex>>,
}

impl Index<MovePathIndex> for PathMap {
    type Output = [MoveOutIndex];
    fn index(&self, index: MovePathIndex) -> &Self::Output {
        assert!(index != INVALID_MOVE_PATH_INDEX);
        &self.map[index.0]
    }
}

/// `MoveOut` represents a point in a program that moves out of some
/// L-value; i.e., "creates" uninitialized memory.
///
/// With respect to dataflow analysis:
/// - Generated by moves and declaration of uninitialized variables.
/// - Killed by assignments to the memory.
#[derive(Copy, Clone)]
pub struct MoveOut {
    /// path being moved
    pub path: MovePathIndex,
    /// location of move
    pub source: Location,
}

impl fmt::Debug for MoveOut {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "p{}@{:?}", self.path.0, self.source)
    }
}

#[derive(Copy, Clone)]
pub struct Location {
    /// block where action is located
    pub block: BasicBlock,
    /// index within above block; statement when < statments.len) or
    /// the terminator (when = statements.len).
    pub index: usize,
}

impl fmt::Debug for Location {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}[{}]", self.block, self.index)
    }
}

pub struct MovePathData<'a, 'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    move_paths: Vec<MovePath<'tcx>>,
}

impl<'a, 'tcx: 'a> Index<MovePathIndex> for MovePathData<'a, 'tcx> {
    type Output = MovePath<'tcx>;
    fn index(&self, i: MovePathIndex) -> &MovePath<'tcx> {
        &self.move_paths[i.idx().unwrap()]
    }
}

/// MovePathRevIndex maps from a uint in an lvalue-category to the
/// MovePathIndex for the MovePath for that lvalue.
type MovePathRevIndex = Vec<MovePathIndex>;

struct MovePathDataBuilder<'a, 'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    pre_move_paths: RefCell<Vec<PreMovePath<'tcx>>>,
    rev_lookup: RefCell<MovePathLookup<'tcx>>,
}

pub struct MovePathLookup<'tcx> {
    vars: MovePathRevIndex,
    temps: MovePathRevIndex,
    args: MovePathRevIndex,
    statics: FnvHashMap<DefId, MovePathIndex>,
    return_ptr: Option<MovePathIndex>,

    /// This is the only non-trivial lookup to explain: projections
    /// are made from a base-lvalue and a projection elem. The
    /// base-lvalue will have a unique MovePathIndex; we use the
    /// latter as the index into the outer vector (narrowing
    /// subsequent search so that it is solely relative to that
    /// base-lvalue). For the remaining lookup, we map the projection
    /// elem to the associated MovePathIndex.
    projections: Vec<FnvHashMap<AbstractElem<'tcx>, MovePathIndex>>,
    next_index: MovePathIndex,
}

trait FillTo {
    type T;
    fn fill_to_with(&mut self, idx: usize, x: Self::T);
    fn fill_to(&mut self, idx: usize) where Self::T: Default {
        self.fill_to_with(idx, Default::default())
    }
}
impl<T:Clone> FillTo for Vec<T> {
    type T = T;
    fn fill_to_with(&mut self, idx: usize, x: T) {
        if idx >= self.len() {
            let delta = idx + 1 - self.len();
            assert_eq!(idx + 1, self.len() + delta);
            self.extend(iter::repeat(x).take(delta))
        }
        debug_assert!(idx < self.len());
    }
}

#[derive(Clone, Debug)]
enum LookupKind { Generate, Reuse }
struct Lookup<T>(LookupKind, T);

impl Lookup<MovePathIndex> {
    fn idx(&self) -> usize { (self.1).0 }
}

impl<'tcx> MovePathLookup<'tcx> {
    fn new() -> Self {
        MovePathLookup {
            vars: vec![],
            temps: vec![],
            args: vec![],
            statics: Default::default(),
            return_ptr: None,
            projections: vec![],
            next_index: MovePathIndex(0),
        }
    }

    fn next_index(next: &mut MovePathIndex) -> MovePathIndex {
        let i = *next;
        *next = MovePathIndex(i.0 + 1);
        i
    }

    fn lookup_or_generate(vec: &mut Vec<MovePathIndex>,
                          idx: u32,
                          next_index: &mut MovePathIndex) -> Lookup<MovePathIndex> {
        let idx = idx as usize;
        vec.fill_to_with(idx, INVALID_MOVE_PATH_INDEX);
        let entry = &mut vec[idx];
        if *entry == INVALID_MOVE_PATH_INDEX {
            let i = Self::next_index(next_index);
            *entry = i;
            Lookup(LookupKind::Generate, i)
        } else {
            Lookup(LookupKind::Reuse, *entry)
        }
    }

    fn lookup_var(&mut self, var_idx: u32) -> Lookup<MovePathIndex> {
        Self::lookup_or_generate(&mut self.vars,
                                 var_idx,
                                 &mut self.next_index)
    }

    fn lookup_temp(&mut self, temp_idx: u32) -> Lookup<MovePathIndex> {
        Self::lookup_or_generate(&mut self.temps,
                                 temp_idx,
                                 &mut self.next_index)
    }

    fn lookup_arg(&mut self, arg_idx: u32) -> Lookup<MovePathIndex> {
        Self::lookup_or_generate(&mut self.args,
                                 arg_idx,
                                 &mut self.next_index)
    }

    fn lookup_static(&mut self, static_id: DefId) -> Lookup<MovePathIndex> {
        let &mut MovePathLookup { ref mut statics,
                                  ref mut next_index, .. } = self;
        match statics.entry(static_id.clone()) {
            Entry::Occupied(ent) => {
                Lookup(LookupKind::Reuse, *ent.get())
            }
            Entry::Vacant(ent) => {
                let mpi = Self::next_index(next_index);
                ent.insert(mpi);
                Lookup(LookupKind::Generate, mpi)
            }
        }
    }

    fn lookup_return_pointer(&mut self) -> Lookup<MovePathIndex> {
        match self.return_ptr {
            Some(mpi) => {
                Lookup(LookupKind::Reuse, mpi)
            }
            ref mut ret @ None => {
                let mpi = Self::next_index(&mut self.next_index);
                *ret = Some(mpi);
                Lookup(LookupKind::Generate, mpi)
            }
        }
    }

    fn lookup_proj(&mut self,
                   proj: &repr::LvalueProjection<'tcx>,
                   base: MovePathIndex) -> Lookup<MovePathIndex> {
        let MovePathLookup { ref mut projections,
                             ref mut next_index, .. } = *self;
        projections.fill_to(base.0);
        match projections[base.0].entry(proj.elem.lift()) {
            Entry::Occupied(ent) => {
                Lookup(LookupKind::Reuse, *ent.get())
            }
            Entry::Vacant(ent) => {
                let mpi = Self::next_index(next_index);
                ent.insert(mpi);
                Lookup(LookupKind::Generate, mpi)
            }
        }
    }
}

impl<'tcx> MovePathLookup<'tcx> {
    // Unlike the builder `fn move_path_for` below, this lookup
    // alternative will *not* create a MovePath on the fly for an
    // unknown l-value; it will simply panic.
    pub fn find(&self, lval: &Lvalue<'tcx>) -> MovePathIndex {
        match *lval {
            Lvalue::Var(var_idx) => self.vars[var_idx as usize],
            Lvalue::Temp(temp_idx) => self.temps[temp_idx as usize],
            Lvalue::Arg(arg_idx) => self.args[arg_idx as usize],
            Lvalue::Static(ref def_id) => self.statics[def_id],
            Lvalue::ReturnPointer => self.return_ptr.unwrap(),
            Lvalue::Projection(ref proj) => {
                let base_index = self.find(&proj.base);
                self.projections[base_index.0 as usize][&proj.elem.lift()]
            }
        }
    }
}

impl<'a, 'tcx> MovePathDataBuilder<'a, 'tcx> {
    // (use of `&self` here is going to necessitate use of e.g. RefCell
    //  or some other &-safe data accumulator)
    //
    // Caller must ensure self's RefCells (i.e. `self.pre_move_paths`
    // and `self.rev_lookup`) are not mutably borrowed.
    fn move_path_for(&self, lval: &Lvalue<'tcx>) -> MovePathIndex {
        let lookup = {
            let mut rev_lookup = self.rev_lookup.borrow_mut();
            match *lval {
                Lvalue::Var(var_idx) => rev_lookup.lookup_var(var_idx),
                Lvalue::Temp(temp_idx) => rev_lookup.lookup_temp(temp_idx),
                Lvalue::Arg(arg_idx) => rev_lookup.lookup_arg(arg_idx),
                Lvalue::Static(def_id) => rev_lookup.lookup_static(def_id),
                Lvalue::ReturnPointer => rev_lookup.lookup_return_pointer(),
                Lvalue::Projection(ref proj) => {
                    // Manually drop the rev_lookup ...
                    drop(rev_lookup);

                    // ... so that we can reborrow it here (which may
                    //     well be building new move path) ...
                    let base_index = self.move_path_for(&proj.base);

                    // ... and restablish exclusive access here.
                    let mut rev_lookup = self.rev_lookup.borrow_mut();
                    rev_lookup.lookup_proj(proj, base_index)
                }
            }
        };

        let mut pre_move_paths = self.pre_move_paths.borrow_mut();

        // At this point, `lookup` is either the previously assigned
        // index or a newly-allocated one.
        debug_assert!(lookup.idx() <= pre_move_paths.len());

        if let Lookup(LookupKind::Generate, mpi) = lookup {
            let parent;
            let sibling;

            match *lval {
                Lvalue::Var(_) | Lvalue::Temp(_) | Lvalue::Arg(_) |
                Lvalue::Static(_) | Lvalue::ReturnPointer => {
                    sibling = INVALID_MOVE_PATH_INDEX;
                    parent = INVALID_MOVE_PATH_INDEX;
                }
                Lvalue::Projection(ref proj) => {
                    // Here, install new MovePath as new first_child.

                    drop(pre_move_paths);

                    // Note: `parent` previously allocated (Projection
                    // case of match above established this).
                    parent = self.move_path_for(&proj.base);

                    pre_move_paths = self.pre_move_paths.borrow_mut();
                    let parent_move_path = &mut pre_move_paths[parent.0];

                    // At last: Swap in the new first_child.
                    sibling = parent_move_path.first_child.get();
                    parent_move_path.first_child.set(mpi);
                }
            };

            let move_path = PreMovePath {
                next_sibling: sibling,
                parent: parent,
                lvalue: lval.clone(),
                first_child: Cell::new(INVALID_MOVE_PATH_INDEX),
            };

            pre_move_paths.push(move_path);
        }

        return lookup.1;
    }
}

impl<'a, 'tcx> MoveData<'a, 'tcx> {
    pub fn gather_moves(mir: &'a Mir<'tcx>, tcx: &ty::ctxt<'tcx>) -> Self {
        gather_moves(mir, tcx)
    }
}

#[derive(Debug)]
enum StmtKind { Use, Repeat, Cast, BinaryOp, UnaryOp, Box, Aggregate, Drop, CallFn, CallArg, }

fn gather_moves<'a, 'tcx>(mir: &'a Mir<'tcx>, tcx: &ty::ctxt<'tcx>) -> MoveData<'a, 'tcx> {
    use self::StmtKind as SK;

    let bbs = mir.all_basic_blocks();
    let mut moves = Vec::with_capacity(bbs.len());
    let mut loc_map: Vec<_> = iter::repeat(Vec::new()).take(bbs.len()).collect();
    let mut path_map = Vec::new();

    let mut builder = MovePathDataBuilder {
        mir: mir,
        pre_move_paths: RefCell::new(Vec::new()),
        rev_lookup: RefCell::new(MovePathLookup::new()),
    };

    struct BlockContext<'b, 'a: 'b, 'tcx: 'a> {
        tcx: &'b ty::ctxt<'tcx>,
        moves: &'b mut Vec<MoveOut>,
        builder: &'b MovePathDataBuilder<'a, 'tcx>,
        path_map: &'b mut Vec<Vec<MoveOutIndex>>,
        loc_map_bb: &'b mut Vec<Vec<MoveOutIndex>>,
    }

    impl<'b, 'a: 'b, 'tcx: 'a> BlockContext<'b, 'a, 'tcx> {
        fn on_move_out_lval(&mut self, stmt_kind: SK, lval: &repr::Lvalue<'tcx>, source: Location) {
            let builder = self.builder;
            let tcx = self.tcx;
            let lval_ty = builder.mir.lvalue_ty(tcx, lval);

            // FIXME: does lvalue_ty ever return TyError, or is it
            // guaranteed to always return non-Infer/non-Error values?

            // This code is just trying to avoid creating a MoveOut
            // entry for values that do not need move semantics.
            //
            // type_contents is imprecise (may claim needs drop for
            // types that in fact have no destructor). But that is
            // still usable for our purposes here.
            let consumed = lval_ty.to_ty(tcx).type_contents(tcx).needs_drop(tcx);

            if !consumed {
                debug!("ctxt: {:?} no consume of lval: {:?} of type {:?}",
                       stmt_kind, lval, lval_ty);
                return;
            }
            let i = source.index;
            let index = MoveOutIndex(self.moves.len());

            let path = builder.move_path_for(lval);
            self.moves.push(MoveOut { path: path, source: source.clone() });
            self.path_map.fill_to(path.0);

            debug!("ctxt: {:?} add consume of lval: {:?} \
                    at index: {:?} \
                    to path_map for path: {:?} and \
                    to loc_map for loc: {:?}",
                   stmt_kind, lval, index, path, source);

            debug_assert!(path.0 < self.path_map.len());
            // this is actually a questionable assert; at the very
            // least, incorrect input code can probably cause it to
            // fire.
            assert!(self.path_map[path.0].iter().find(|idx| **idx == index).is_none());
            self.path_map[path.0].push(index);

            debug_assert!(i < self.loc_map_bb.len());
            debug_assert!(self.loc_map_bb[i].iter().find(|idx| **idx == index).is_none());
            self.loc_map_bb[i].push(index);
        }

        fn on_operand(&mut self, stmt_kind: SK, operand: &repr::Operand<'tcx>, source: Location) {
            match *operand {
                repr::Operand::Constant(..) => {} // not-a-move
                repr::Operand::Consume(ref lval) => { // a move
                    self.on_move_out_lval(stmt_kind, lval, source);
                }
            }
        }
    }

    for bb in bbs {
        let loc_map_bb = &mut loc_map[bb.index()];
        let bb_data = mir.basic_block_data(bb);

        debug_assert!(loc_map_bb.len() == 0);
        let len = bb_data.statements.len();
        loc_map_bb.fill_to(len);
        debug_assert!(loc_map_bb.len() == len + 1);

        let mut bb_ctxt = BlockContext {
            tcx: tcx, moves: &mut moves, builder: &builder, path_map: &mut path_map, loc_map_bb: loc_map_bb,
        };

        for (i, stmt) in bb_data.statements.iter().enumerate() {
            let source = Location { block: bb, index: i };
            match stmt.kind {
                StatementKind::Assign(ref lval, ref rval) => {
                    // ensure MovePath created for `lval`.
                    builder.move_path_for(lval);

                    match *rval {
                        Rvalue::Use(ref operand) => {
                            bb_ctxt.on_operand(SK::Use, operand, source)
                        }
                        Rvalue::Repeat(ref operand, ref _const) =>
                            bb_ctxt.on_operand(SK::Repeat, operand, source),
                        Rvalue::Cast(ref _kind, ref operand, ref _ty) =>
                            bb_ctxt.on_operand(SK::Cast, operand, source),
                        Rvalue::BinaryOp(ref _binop, ref operand1, ref operand2) => {
                            bb_ctxt.on_operand(SK::BinaryOp, operand1, source);
                            bb_ctxt.on_operand(SK::BinaryOp, operand2, source);
                        }
                        Rvalue::UnaryOp(ref _unop, ref operand) => {
                            bb_ctxt.on_operand(SK::UnaryOp, operand, source);
                        }
                        Rvalue::Box(ref _ty) => {
                            // this is creating uninitialized
                            // memory that needs to be initialized.
                            bb_ctxt.on_move_out_lval(SK::Box, lval, source);
                        }
                        Rvalue::Aggregate(ref _kind, ref operands) => {
                            for operand in operands {
                                bb_ctxt.on_operand(SK::Aggregate, operand, source);
                            }
                        }
                        Rvalue::Slice {..} => panic!("cannot move out of slice"),
                        Rvalue::Ref(..) |
                        Rvalue::Len(..) |
                        Rvalue::InlineAsm(..) => {}
                    }
                }
            }
        }

        if let Some(ref term) = bb_data.terminator {
            match *term {
                Terminator::Goto { target: _ } | Terminator::Resume => { }

                Terminator::Return => {
                    // One might reasonably wonder for the Return
                    // case: Do we need to treat this as a move out of
                    // the ReturnPointer lvalue?
                    //
                    // (Seems unlikely; all drops should have been
                    // explicitly handled *before* this point, and
                    // therefore there should not be any code that
                    // could actually attempt to interfere with such a
                    // move. Keep in mind that the moves here are
                    // tracking *deinitialization* of memory.)
                }

                Terminator::If { ref cond, targets: _ } => {
                    // The `cond` is always of (copyable) type `bool`,
                    // so there will never be anything to move.
                    let _ = cond;
                }

                Terminator::SwitchInt { switch_ty: _, values: _, targets: _, ref discr } |
                Terminator::Switch { adt_def: _, targets: _, ref discr } => {
                    // The `discr` is not consumed; that is instead
                    // encoded on specific match arms (and for
                    // SwitchInt`, it is always a copyable integer
                    // type anyway).
                    let _ = discr;
                }

                Terminator::Drop { value: ref lval, ref target, ref unwind } => {
                    let source = Location { block: bb,
                                            index: bb_data.statements.len() };
                    bb_ctxt.on_move_out_lval(SK::Drop, lval, source);
                }

                Terminator::Call { ref func, ref args, ref destination, ref cleanup } => {
                    let source = Location { block: bb,
                                            index: bb_data.statements.len() };
                    bb_ctxt.on_operand(SK::CallFn, func, source);
                    for arg in args {
                        bb_ctxt.on_operand(SK::CallArg, arg, source);
                    }
                    if let Some((ref destination, ref bb)) = *destination {
                        // Create MovePath for `destination`, then
                        // discard returned index.
                        builder.move_path_for(destination);
                    }
                }
            }
        }
    }


    // At this point, we may have created some MovePaths that do not
    // have corresponding entries in the path map. Address that now.
    path_map.fill_to(builder.pre_move_paths.borrow().len() - 1);

    let pre_move_paths = builder.pre_move_paths.into_inner();
    let move_paths: Vec<_> = pre_move_paths.into_iter()
        .map(|p| p.into_move_path())
        .collect();

    {
        // This block is just debug instrumentation
        let mut seen: Vec<_> = move_paths.iter().map(|_| false).collect();
        for (j, &MoveOut { ref path, ref source }) in moves.iter().enumerate() {
            debug!("MovePathData moves[{}]: MoveOut {{ path: {:?} = {:?}, source: {:?} }}",
                   j, path, move_paths[path.0], source);
            seen[path.0] = true;
        }
        for (j, path) in move_paths.iter().enumerate() {
            if !seen[j] {
                debug!("MovePathData move_paths[{}]: {:?}", j, path);
            }
        }
    }

    MoveData { move_paths: MovePathData { mir: builder.mir,
                                          move_paths: move_paths, },
               moves: moves,
               loc_map: LocMap { map: loc_map },
               path_map: PathMap { map: path_map },
               rev_lookup: builder.rev_lookup.into_inner(),
    }
}

impl<'a, 'tcx> BitDenotation for MoveData<'a, 'tcx>{
    type Bit = MoveOut;
    fn bits_per_block(&self) -> usize {
        self.moves.len()
    }
    fn interpret(&self, idx: usize) -> &Self::Bit {
        &self.moves[idx]
    }
}
