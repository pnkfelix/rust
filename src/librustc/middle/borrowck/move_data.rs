// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

Data structures used for tracking moves. Please see the extensive
comments in the section "Moves and initialization" and in `doc.rs`.

*/

use std::cell::RefCell;
use std::rc::Rc;
use std::uint;
use std::collections::{HashMap, HashSet};
use middle::borrowck::*;
use middle::cfg;
use middle::dataflow::DataFlowContext;
use middle::dataflow::BitwiseOperator;
use middle::dataflow::DataFlowOperator;
use euv = middle::expr_use_visitor;
use mc = middle::mem_categorization;
use middle::ty;
use syntax::ast;
use syntax::ast_map;
use syntax::ast_util;
use syntax::codemap::Span;
use util::ppaux::Repr;

pub struct MoveData {
    /// Move paths. See section "Move paths" in `doc.rs`.
    pub paths: RefCell<Vec<MovePath>>,

    /// Cache of loan path to move path index, for easy lookup.
    pub path_map: RefCell<HashMap<Rc<LoanPath>, MovePathIndex>>,

    /// Each move or uninitialized variable gets an entry here.
    pub moves: RefCell<Vec<Move>>,

    /// Assignments to a variable, like `x = foo`. These are assigned
    /// bits for dataflow, since we must track them to ensure that
    /// immutable variables are assigned at most once along each path.
    pub var_assignments: RefCell<Vec<Assignment>>,

    /// Assignments to a path, like `x.f = foo`. These are not
    /// assigned dataflow bits, but we track them because they still
    /// kill move bits.
    pub path_assignments: RefCell<Vec<Assignment>>,

    /// Assignments to a variable or path, like `x = foo`, but not `x += foo`.
    pub assignee_ids: RefCell<HashSet<ast::NodeId>>,
}

pub struct FlowedMoveData<'a> {
    pub move_data: MoveData,

    pub dfcx_moves: MoveDataFlow<'a>,

    // We could (and maybe should, for efficiency) combine both move
    // and assign data flow into one, but this way it's easier to
    // distinguish the bits that correspond to moves and assignments.
    pub dfcx_assign: AssignDataFlow<'a>,

    pub dfcx_needs_drop: NeedsDropDataFlow<'a>,
}

/// Index into `MoveData.paths`, used like a pointer
#[deriving(PartialEq)]
// FIXME: should not be `pub`. Revise dataflow to support abstractions like this.
pub struct MovePathIndex(pub uint);

impl MovePathIndex {
    fn get(&self) -> uint {
        let MovePathIndex(v) = *self; v
    }
}

impl Clone for MovePathIndex {
    fn clone(&self) -> MovePathIndex {
        MovePathIndex(self.get())
    }
}

static InvalidMovePathIndex: MovePathIndex =
    MovePathIndex(uint::MAX);

/// Index into `MoveData.moves`, used like a pointer
#[deriving(PartialEq)]
pub struct MoveIndex(uint);

impl MoveIndex {
    fn get(&self) -> uint {
        let MoveIndex(v) = *self; v
    }
}

static InvalidMoveIndex: MoveIndex =
    MoveIndex(uint::MAX);

pub struct MovePath {
    /// Loan path corresponding to this move path
    pub loan_path: Rc<LoanPath>,

    /// Parent pointer, `InvalidMovePathIndex` if root
    pub parent: MovePathIndex,

    /// Head of linked list of moves to this path,
    /// `InvalidMoveIndex` if not moved
    pub first_move: MoveIndex,

    /// First node in linked list of children, `InvalidMovePathIndex` if leaf
    pub first_child: MovePathIndex,

    /// Next node in linked list of parent's children (siblings),
    /// `InvalidMovePathIndex` if none.
    pub next_sibling: MovePathIndex,
}

#[deriving(PartialEq)]
pub enum MoveKind {
    Declared,   // When declared, variables start out "moved".
    MoveExpr,   // Expression or binding that moves a variable
    MovePat,    // By-move binding
    Captured    // Closure creation that moves a value
}

pub struct Move {
    /// Path being moved.
    pub path: MovePathIndex,

    /// id of node that is doing the move.
    pub id: ast::NodeId,

    /// Kind of move, for error messages.
    pub kind: MoveKind,

    /// Next node in linked list of moves from `path`, or `InvalidMoveIndex`
    pub next_move: MoveIndex
}

pub struct Assignment {
    /// Path being assigned.
    pub path: MovePathIndex,

    /// id where assignment occurs
    pub id: ast::NodeId,

    /// span of node where assignment occurs
    pub span: Span,
}

#[deriving(Clone)]
pub struct MoveDataFlowOperator;

pub type MoveDataFlow<'a> = DataFlowContext<'a, MoveDataFlowOperator>;

#[deriving(Clone)]
pub struct AssignDataFlowOperator;

pub type AssignDataFlow<'a> = DataFlowContext<'a, AssignDataFlowOperator>;

#[deriving(Clone)]
pub struct NeedsDropDataFlowOperator;
pub type NeedsDropDataFlow<'a> = DataFlowContext<'a, NeedsDropDataFlowOperator>;

fn loan_path_is_precise(loan_path: &LoanPath) -> bool {
    match *loan_path {
        LpVar(_) | LpUpvar(_) => {
            true
        }
        LpExtend(_, _, LpInterior(mc::InteriorElement(_))) => {
            // Paths involving element accesses do not refer to a unique
            // location, as there is no accurate tracking of the indices.
            false
        }
        LpExtend(ref lp_base, _, _) => {
            loan_path_is_precise(&**lp_base)
        }
    }
}

impl Move {
    pub fn ty_and_span(&self, tcx: &ty::ctxt) -> (ty::t, Span) {
        match self.kind {
            Declared  => unimplemented!(),
            MovePat => (ty::node_id_to_type(tcx, self.id), tcx.map.span(self.id)),
            MoveExpr | Captured => match tcx.map.find(self.id) {
                Some(ast_map::NodeExpr(expr)) =>
                    (ty::expr_ty_adjusted(tcx, &*expr), expr.span),
                r => tcx.sess.bug(format!("{:?}({:?}) maps to {:?}, not Expr",
                                          self.kind, self.id, r).as_slice())
            },
        }
    }

    pub fn ty(&self, tcx: &ty::ctxt) -> ty::t {
        self.ty_and_span(tcx).val0()
    }

    pub fn to_string(&self, move_data: &MoveData, tcx: &ty::ctxt) -> String {
        format!("Move{:s} path: {}, id: {}, kind: {:?} {:s}",
                "{",
                move_data.path_loan_path(self.path).repr(tcx),
                self.id,
                self.kind,
                "}")
    }
}

impl Assignment {
    pub fn ty_and_span(&self, tcx: &ty::ctxt) -> (ty::t, Span) {
        match tcx.map.find(self.id) {
            Some(ast_map::NodeExpr(expr)) =>
                (ty::expr_ty_adjusted(tcx, &*expr), expr.span),
            Some(ast_map::NodeLocal(pat)) =>
                (ty::node_id_to_type(tcx, pat.id), tcx.map.span(pat.id)),
            r => tcx.sess.bug(format!("{:?} maps to {:?}, not Expr", self, r).as_slice())
        }
    }
    pub fn ty(&self, tcx: &ty::ctxt) -> ty::t {
        self.ty_and_span(tcx).val0()
    }
    pub fn to_string(&self, move_data: &MoveData, tcx: &ty::ctxt) -> String {
        format!("Assignment{:s} path: {}, id: {} {:s}",
                "{",
                move_data.path_loan_path(self.path).repr(tcx),
                self.id,
                "}")
    }
}

impl MoveData {
    pub fn new() -> MoveData {
        MoveData {
            paths: RefCell::new(Vec::new()),
            path_map: RefCell::new(HashMap::new()),
            moves: RefCell::new(Vec::new()),
            path_assignments: RefCell::new(Vec::new()),
            var_assignments: RefCell::new(Vec::new()),
            assignee_ids: RefCell::new(HashSet::new()),
        }
    }

    pub fn path_loan_path(&self, index: MovePathIndex) -> Rc<LoanPath> {
        self.paths.borrow().get(index.get()).loan_path.clone()
    }

    fn path_parent(&self, index: MovePathIndex) -> MovePathIndex {
        self.paths.borrow().get(index.get()).parent
    }

    fn path_first_move(&self, index: MovePathIndex) -> MoveIndex {
        self.paths.borrow().get(index.get()).first_move
    }

    fn path_first_child(&self, index: MovePathIndex) -> MovePathIndex {
        self.paths.borrow().get(index.get()).first_child
    }

    fn path_next_sibling(&self, index: MovePathIndex) -> MovePathIndex {
        self.paths.borrow().get(index.get()).next_sibling
    }

    fn set_path_first_move(&self,
                           index: MovePathIndex,
                           first_move: MoveIndex) {
        self.paths.borrow_mut().get_mut(index.get()).first_move = first_move
    }

    fn set_path_first_child(&self,
                            index: MovePathIndex,
                            first_child: MovePathIndex) {
        self.paths.borrow_mut().get_mut(index.get()).first_child = first_child
    }

    fn move_next_move(&self, index: MoveIndex) -> MoveIndex {
        //! Type safe indexing operator
        self.moves.borrow().get(index.get()).next_move
    }

    fn is_var_path(&self, index: MovePathIndex) -> bool {
        //! True if `index` refers to a variable
        self.path_parent(index) == InvalidMovePathIndex
    }

    pub fn move_path(&self,
                     tcx: &ty::ctxt,
                     lp: Rc<LoanPath>) -> MovePathIndex {
        /*!
         * Returns the existing move path index for `lp`, if any,
         * and otherwise adds a new index for `lp` and any of its
         * base paths that do not yet have an index.
         */

        match self.path_map.borrow().find(&lp) {
            Some(&index) => {
                return index;
            }
            None => {}
        }

        let index = match *lp {
            LpVar(..) | LpUpvar(..) => {
                let index = MovePathIndex(self.paths.borrow().len());

                self.paths.borrow_mut().push(MovePath {
                    loan_path: lp.clone(),
                    parent: InvalidMovePathIndex,
                    first_move: InvalidMoveIndex,
                    first_child: InvalidMovePathIndex,
                    next_sibling: InvalidMovePathIndex,
                });

                index
            }

            LpExtend(ref base, _, _) => {
                let parent_index = self.move_path(tcx, base.clone());

                let index = MovePathIndex(self.paths.borrow().len());

                let next_sibling = self.path_first_child(parent_index);
                self.set_path_first_child(parent_index, index);

                self.paths.borrow_mut().push(MovePath {
                    loan_path: lp.clone(),
                    parent: parent_index,
                    first_move: InvalidMoveIndex,
                    first_child: InvalidMovePathIndex,
                    next_sibling: next_sibling,
                });

                index
            }
        };

        debug!("move_path(lp={}, index={:?})",
               lp.repr(tcx),
               index);

        assert_eq!(index.get(), self.paths.borrow().len() - 1);
        self.path_map.borrow_mut().insert(lp, index);
        return index;
    }

    fn existing_move_path(&self, lp: &Rc<LoanPath>)
                          -> Option<MovePathIndex> {
        self.path_map.borrow().find_copy(lp)
    }

    fn existing_base_paths(&self, lp: &Rc<LoanPath>)
                           -> Vec<MovePathIndex> {
        let mut result = vec!();
        self.add_existing_base_paths(lp, &mut result);
        result
    }

    fn add_existing_base_paths(&self, lp: &Rc<LoanPath>,
                               result: &mut Vec<MovePathIndex>) {
        /*!
         * Adds any existing move path indices for `lp` and any base
         * paths of `lp` to `result`, but does not add new move paths
         */

        match self.path_map.borrow().find_copy(lp) {
            Some(index) => {
                self.each_base_path(index, |p| {
                    result.push(p);
                    true
                });
            }
            None => {
                match **lp {
                    LpVar(..) | LpUpvar(..) => { }
                    LpExtend(ref b, _, _) => {
                        self.add_existing_base_paths(b, result);
                    }
                }
            }
        }

    }

    pub fn add_move(&self,
                    tcx: &ty::ctxt,
                    lp: Rc<LoanPath>,
                    id: ast::NodeId,
                    kind: MoveKind) {
        /*!
         * Adds a new move entry for a move of `lp` that occurs at
         * location `id` with kind `kind`.
         */

        debug!("add_move(lp={}, id={:?}, kind={:?})",
               lp.repr(tcx),
               id,
               kind);

        let path_index = self.move_path(tcx, lp);
        let move_index = MoveIndex(self.moves.borrow().len());

        let next_move = self.path_first_move(path_index);
        self.set_path_first_move(path_index, move_index);

        self.moves.borrow_mut().push(Move {
            path: path_index,
            id: id,
            kind: kind,
            next_move: next_move
        });
    }

    pub fn add_assignment(&self,
                          tcx: &ty::ctxt,
                          lp: Rc<LoanPath>,
                          assign_id: ast::NodeId,
                          span: Span,
                          assignee_id: ast::NodeId,
                          mode: euv::MutateMode) {
        /*!
         * Adds a new record for an assignment to `lp` that occurs at
         * location `id` with the given `span`.
         */

        debug!("add_assignment(lp={}, assign_id={:?}, assignee_id={:?}",
               lp.repr(tcx), assign_id, assignee_id);

        let path_index = self.move_path(tcx, lp.clone());

        match mode {
            euv::Init | euv::JustWrite => {
                self.assignee_ids.borrow_mut().insert(assignee_id);
            }
            euv::WriteAndRead => { }
        }

        let assignment = Assignment {
            path: path_index,
            id: assign_id,
            span: span,
        };

        if self.is_var_path(path_index) {
            debug!("add_assignment[var](lp={}, assignment={}, path_index={:?})",
                   lp.repr(tcx), self.var_assignments.borrow().len(), path_index);

            self.var_assignments.borrow_mut().push(assignment);
        } else {
            debug!("add_assignment[path](lp={}, path_index={:?})",
                   lp.repr(tcx), path_index);

            self.path_assignments.borrow_mut().push(assignment);
        }
    }

    fn add_gen_kills(&self,
                     tcx: &ty::ctxt,
                     dfcx_moves: &mut MoveDataFlow,
                     dfcx_assign: &mut AssignDataFlow,
                     dfcx_needs_drop: &mut NeedsDropDataFlow) {
        /*!
         * Adds the gen/kills for the various moves and
         * assignments into the provided data flow contexts.
         * Moves are generated by moves and killed by assignments and
         * scoping. Assignments are generated by assignment to variables and
         * killed by scoping.  Drop obligations (aka "Needs-Drop") are
         * generated by assignments and killed by moves and scoping. by
         * See `doc.rs` for more details.
         */

        for (i, move) in self.moves.borrow().iter().enumerate() {
            dfcx_moves.add_gen(move.id, i);
            debug!("remove_drop_obligations move {}", move.to_string(self, tcx));
            self.remove_drop_obligation(move, dfcx_needs_drop);
        }

        for (i, assignment) in self.var_assignments.borrow().iter().enumerate() {
            dfcx_assign.add_gen(assignment.id, i);
            self.kill_moves(assignment.path, assignment.id, dfcx_moves);
            debug!("add_drop_obligations var_assignment {}", assignment.to_string(self, tcx));
            self.add_drop_obligations(tcx, assignment, dfcx_needs_drop);
        }

        for assignment in self.path_assignments.borrow().iter() {
            self.kill_moves(assignment.path, assignment.id, dfcx_moves);
            debug!("add_drop_obligations path_assignment {}", assignment.to_string(self, tcx));
            self.add_drop_obligations(tcx, assignment, dfcx_needs_drop);
        }

        // Kill all moves and drop-obligations related to a variable `x` when
        // it goes out of scope:
        for path in self.paths.borrow().iter() {
            match *path.loan_path {
                LpVar(id) => {
                    let kill_id = tcx.region_maps.var_scope(id);
                    let path = *self.path_map.borrow().get(&path.loan_path);
                    self.kill_moves(path, kill_id, dfcx_moves);
                    self.remove_drop_obligation(
                        Removed { where: kill_id, what_path: path }, dfcx_needs_drop);
                }
                LpUpvar(ty::UpvarId { var_id: _, closure_expr_id }) => {
                    let kill_id = closure_to_block(closure_expr_id, tcx);
                    let path = *self.path_map.borrow().get(&path.loan_path);
                    self.kill_moves(path, kill_id, dfcx_moves);
                    self.remove_drop_obligation(
                        Removed { where: kill_id, what_path: path }, dfcx_needs_drop);
                }
                LpExtend(..) => {}
            }
        }

        // Kill all assignments when the variable goes out of scope:
        for (assignment_index, assignment) in
                self.var_assignments.borrow().iter().enumerate() {
            match *self.path_loan_path(assignment.path) {
                LpVar(id) => {
                    let kill_id = tcx.region_maps.var_scope(id);
                    dfcx_assign.add_kill(kill_id, assignment_index);
                }
                LpUpvar(ty::UpvarId { var_id: _, closure_expr_id }) => {
                    let kill_id = closure_to_block(closure_expr_id, tcx);
                    dfcx_assign.add_kill(kill_id, assignment_index);
                }
                LpExtend(..) => {
                    tcx.sess.bug("var assignment for non var path");
                }
            }
        }
    }

    fn each_base_path(&self, index: MovePathIndex, f: |MovePathIndex| -> bool)
                      -> bool {
        let mut p = index;
        while p != InvalidMovePathIndex {
            if !f(p) {
                return false;
            }
            p = self.path_parent(p);
        }
        return true;
    }

    fn each_extending_path(&self,
                           index: MovePathIndex,
                           f: |MovePathIndex| -> bool)
                           -> bool {
        if !f(index) {
            return false;
        }

        let mut p = self.path_first_child(index);
        while p != InvalidMovePathIndex {
            if !self.each_extending_path(p, |x| f(x)) {
                return false;
            }
            p = self.path_next_sibling(p);
        }

        return true;
    }

    fn each_applicable_move(&self,
                            index0: MovePathIndex,
                            f: |MoveIndex| -> bool)
                            -> bool {
        let mut ret = true;
        self.each_extending_path(index0, |index| {
            let mut p = self.path_first_move(index);
            while p != InvalidMoveIndex {
                if !f(p) {
                    ret = false;
                    break;
                }
                p = self.move_next_move(p);
            }
            ret
        });
        ret
    }

    fn kill_moves(&self,
                  path: MovePathIndex,
                  kill_id: ast::NodeId,
                  dfcx_moves: &mut MoveDataFlow) {
        // We can only perform kills for paths that refer to a unique location,
        // since otherwise we may kill a move from one location with an
        // assignment referring to another location.

        let loan_path = self.path_loan_path(path);
        if loan_path_is_precise(&*loan_path) {
            self.each_applicable_move(path, |move_index| {
                dfcx_moves.add_kill(kill_id, move_index.get());
                true
            });
        }
    }

    fn add_drop_obligations(&self,
                            tcx: &ty::ctxt,
                            assignment: &Assignment,
                            dfcx_needs_drop: &mut NeedsDropDataFlow) {
        if ty::type_needs_drop(tcx, assignment.ty(tcx)) {
            dfcx_needs_drop.add_gen(assignment.id, assignment.path.get());
        }
    }

    fn remove_drop_obligation<A:RemoveNeedsDropArg>(&self,
                                                    a: A,
                                                    dfcx_needs_drop: &mut NeedsDropDataFlow) {
        // Kill path and all of its sub-paths.
        // Lets assume we had a pre-existing drop obligation ND = { s.a, s2 },
        // where:
        // ```
        // struct S { a: A, b: B, c: C }
        // struct A { i: I, j: J, k: K }
        // struct J { x: X, y: Y, z: Z }
        // and s : S (and s2 : S as well).
        //
        // Moving `s.a.j.x` implies that:
        // * We no longer have a drop-obligation for s.a in its entirety: ND' := ND \ { s.a }
        // * We now do have drop-obligations for the portions of `s.a` that were not moved:
        //   ND' := ND + { s.a.i, s.a.k }
        // * Likewise, we also have drop-obligations for the portions of `s.a.j` that were
        //   not moved:
        //   ND' := ND + { s.a.j.y, s.a.j.z }
        //
        // Altogether, the above modifications accumulate to:
        // ND' := ND \ { s.a } + { s.a.i, s.a.j.y, s.a.j.z, s.a.k }
        //
        // To simplify constructions like the above let us define taking the derivative
        // of a path P with respect to an appropriate subpath suffix S: d/d{S}(P)
        //
        // So for example, d/d{.j.x}(s.a) := { s.a.i, s.a.j.y, s.a.j.z, s.a.k }
        //
        // TODO: Write definition of d/d{S}(P), presumably by induction on suffix S.

        let id = a.node_id_removing_obligation();
        let path = a.path_being_moved();
        dfcx_needs_drop.add_kill(id, path.get());
    }
}

trait RemoveNeedsDropArg {
    fn node_id_removing_obligation(&self) -> ast::NodeId;
    fn path_being_moved(&self) -> MovePathIndex;
}
struct Removed { where: ast::NodeId, what_path: MovePathIndex }
impl RemoveNeedsDropArg for Removed {
    fn node_id_removing_obligation(&self) -> ast::NodeId { self.where }
    fn path_being_moved(&self) -> MovePathIndex { self.what_path }
}
impl<'a> RemoveNeedsDropArg for &'a Move {
    fn node_id_removing_obligation(&self) -> ast::NodeId { self.id }
    fn path_being_moved(&self) -> MovePathIndex { self.path }
}

impl<'a> FlowedMoveData<'a> {
    pub fn new(move_data: MoveData,
               tcx: &'a ty::ctxt,
               cfg: &cfg::CFG,
               id_range: ast_util::IdRange,
               decl: &ast::FnDecl,
               body: &ast::Block)
               -> FlowedMoveData<'a> {
        let mut dfcx_moves =
            DataFlowContext::new(tcx,
                                 "flowed_move_data_moves",
                                 Some(decl),
                                 cfg,
                                 MoveDataFlowOperator,
                                 id_range,
                                 move_data.moves.borrow().len());
        let mut dfcx_assign =
            DataFlowContext::new(tcx,
                                 "flowed_move_data_assigns",
                                 Some(decl),
                                 cfg,
                                 AssignDataFlowOperator,
                                 id_range,
                                 move_data.var_assignments.borrow().len());
        let mut dfcx_needs_drop =
            DataFlowContext::new(tcx,
                                 "flowed_move_data_needs_drop",
                                 Some(decl),
                                 cfg,
                                 NeedsDropDataFlowOperator,
                                 id_range,
                                 move_data.paths.borrow().len());
        move_data.add_gen_kills(tcx,
                                &mut dfcx_moves,
                                &mut dfcx_assign,
                                &mut dfcx_needs_drop);

        dfcx_moves.add_kills_from_flow_exits(cfg);
        dfcx_assign.add_kills_from_flow_exits(cfg);
        dfcx_needs_drop.add_kills_from_flow_exits(cfg);

        dfcx_moves.propagate(cfg, body);
        dfcx_assign.propagate(cfg, body);
        dfcx_needs_drop.propagate(cfg, body);

        FlowedMoveData {
            move_data: move_data,
            dfcx_moves: dfcx_moves,
            dfcx_assign: dfcx_assign,
            dfcx_needs_drop: dfcx_needs_drop,
        }
    }

    pub fn each_path_moved_by(&self,
                              id: ast::NodeId,
                              f: |&Move, &LoanPath| -> bool)
                              -> bool {
        /*!
         * Iterates through each path moved by `id`
         */

        self.dfcx_moves.each_gen_bit(id, |index| {
            let move = self.move_data.moves.borrow();
            let move = move.get(index);
            let moved_path = move.path;
            f(move, &*self.move_data.path_loan_path(moved_path))
        })
    }

    pub fn kind_of_move_of_path(&self,
                                id: ast::NodeId,
                                loan_path: &Rc<LoanPath>)
                                -> Option<MoveKind> {
        //! Returns the kind of a move of `loan_path` by `id`, if one exists.

        let mut ret = None;
        for loan_path_index in self.move_data.path_map.borrow().find(&*loan_path).iter() {
            self.dfcx_moves.each_gen_bit(id, |move_index| {
                let move = self.move_data.moves.borrow();
                let move = move.get(move_index);
                if move.path == **loan_path_index {
                    ret = Some(move.kind);
                    false
                } else {
                    true
                }
            });
        }
        ret
    }

    pub fn each_move_of(&self,
                        id: ast::NodeId,
                        loan_path: &Rc<LoanPath>,
                        f: |&Move, &LoanPath| -> bool)
                        -> bool {
        /*!
         * Iterates through each move of `loan_path` (or some base path
         * of `loan_path`) that *may* have occurred on entry to `id` without
         * an intervening assignment. In other words, any moves that
         * would invalidate a reference to `loan_path` at location `id`.
         */

        // Bad scenarios:
        //
        // 1. Move of `a.b.c`, use of `a.b.c`
        // 2. Move of `a.b.c`, use of `a.b.c.d`
        // 3. Move of `a.b.c`, use of `a` or `a.b`
        //
        // OK scenario:
        //
        // 4. move of `a.b.c`, use of `a.b.d`

        let base_indices = self.move_data.existing_base_paths(loan_path);
        if base_indices.is_empty() {
            return true;
        }

        let opt_loan_path_index = self.move_data.existing_move_path(loan_path);

        let mut ret = true;

        self.dfcx_moves.each_bit_on_entry(id, |index| {
            let move = self.move_data.moves.borrow();
            let move = move.get(index);
            let moved_path = move.path;
            if base_indices.iter().any(|x| x == &moved_path) {
                // Scenario 1 or 2: `loan_path` or some base path of
                // `loan_path` was moved.
                if !f(move, &*self.move_data.path_loan_path(moved_path)) {
                    ret = false;
                }
            } else {
                for &loan_path_index in opt_loan_path_index.iter() {
                    let cont = self.move_data.each_base_path(moved_path, |p| {
                        if p == loan_path_index {
                            // Scenario 3: some extension of `loan_path`
                            // was moved
                            f(move, &*self.move_data.path_loan_path(moved_path))
                        } else {
                            true
                        }
                    });
                    if !cont { ret = false; break }
                }
            }
            ret
        })
    }

    pub fn is_assignee(&self,
                       id: ast::NodeId)
                       -> bool {
        //! True if `id` is the id of the LHS of an assignment
        self.move_data.assignee_ids.borrow().iter().any(|x| x == &id)
    }

    pub fn each_assignment_of(&self,
                              id: ast::NodeId,
                              loan_path: &Rc<LoanPath>,
                              f: |&Assignment| -> bool)
                              -> bool {
        /*!
         * Iterates through every assignment to `loan_path` that
         * may have occurred on entry to `id`. `loan_path` must be
         * a single variable.
         */

        let loan_path_index = {
            match self.move_data.existing_move_path(loan_path) {
                Some(i) => i,
                None => {
                    // if there were any assignments, it'd have an index
                    return true;
                }
            }
        };

        self.dfcx_assign.each_bit_on_entry(id, |index| {
            let assignment = self.move_data.var_assignments.borrow();
            let assignment = assignment.get(index);
            if assignment.path == loan_path_index && !f(assignment) {
                false
            } else {
                true
            }
        })
    }
}

impl BitwiseOperator for MoveDataFlowOperator {
    #[inline]
    fn join(&self, succ: uint, pred: uint) -> uint {
        succ | pred // moves from both preds are in scope
    }
}

impl DataFlowOperator for MoveDataFlowOperator {
    #[inline]
    fn initial_value(&self) -> bool {
        false // no loans in scope by default
    }
}

impl BitwiseOperator for AssignDataFlowOperator {
    #[inline]
    fn join(&self, succ: uint, pred: uint) -> uint {
        succ | pred // moves from both preds are in scope
    }
}

impl DataFlowOperator for AssignDataFlowOperator {
    #[inline]
    fn initial_value(&self) -> bool {
        false // no assignments in scope by default
    }
}

impl BitwiseOperator for NeedsDropDataFlowOperator {
    #[inline]
    fn join(&self, succ: uint, pred: uint) -> uint {
        // In principle, for correct code, the fixed-point solution
        // to the dataflow equations will have succ == pred here.
        //
        // But since we need to deal with states before we hit the
        // fixed point, we use logical-or here, to properly handle cases
        // like a while loop:
        //   `{ let a = box 3; while <cond> { <body> } <rest> }`
        // where <cond> and <body> do not move or drop `a`:
        //
        //         [let a = box 3;]
        //           |
        //           v 1
        //       [loopback] <--+ 5
        //           |         |
        //           v 2       |
        //   +-----[cond]      |
        //   |       |         |
        //   |       v 4       |
        //   |     [body] -----+
        //   v 3
        // [rest]
        //
        // we need to ensure that the fixed-point solution registers
        // that `a` is needs-drop on all of the above edges.
        // Logical-or will accomplish that here (while logical-and
        // would cause the fixed point solution to falsely claim that
        // `a` is only needs-drop on edge 1.

        succ | pred
    }
}

impl DataFlowOperator for NeedsDropDataFlowOperator {
    #[inline]
    fn initial_value(&self) -> bool {
        false // paths uninitialized by default and thus do not need dropping
    }
}
