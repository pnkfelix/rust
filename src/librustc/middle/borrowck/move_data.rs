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
use middle::expr_use_visitor as euv;
use middle::mem_categorization as mc;
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

    /// Enum variant matched within a pattern on some match arm, like
    /// `SomeStruct{ f: Variant1(x, y) } => ...`
    pub variant_matches: RefCell<Vec<VariantMatch>>,

    /// Assignments to a variable or path, like `x = foo`, but not `x += foo`.
    pub assignee_ids: RefCell<HashSet<ast::NodeId>>,

    /// During move_data construction, `fragments` tracks paths that
    /// *might* be needs-drop leftovers.  When move_data has been
    /// completed, `fragments` tracks paths that are *definitely*
    /// needs-drop left-overs.
    pub fragments: RefCell<Vec<MovePathIndex>>,

    /// `nonfragments` always tracks paths that have been definitely
    /// used directly in moves).
    pub nonfragments: RefCell<Vec<MovePathIndex>>,
}

pub struct FlowedMoveData<'a, 'tcx: 'a> {
    pub move_data: MoveData,

    pub dfcx_moves: MoveDataFlow<'a, 'tcx>,

    // We could (and maybe should, for efficiency) combine both move
    // and assign data flow into one, but this way it's easier to
    // distinguish the bits that correspond to moves and assignments.
    pub dfcx_assign: AssignDataFlow<'a, 'tcx>

    pub dfcx_needs_drop: NeedsDropDataFlow<'a, 'tcx>,
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

pub struct VariantMatch {
    /// downcast to the variant.
    pub path: MovePathIndex,

    /// path being downcast to the variant.
    pub base_path: MovePathIndex,

    /// id where variant's pattern occurs
    pub id: ast::NodeId,
}

#[deriving(Clone)]
pub struct MoveDataFlowOperator;

pub type MoveDataFlow<'a, 'tcx> = DataFlowContext<'a, 'tcx, MoveDataFlowOperator>;

#[deriving(Clone)]
pub struct AssignDataFlowOperator;

pub type AssignDataFlow<'a, 'tcx> = DataFlowContext<'a, 'tcx, AssignDataFlowOperator>;

#[deriving(Clone)]
pub struct NeedsDropDataFlowOperator;
pub type NeedsDropDataFlow<'a> = DataFlowContext<'a, NeedsDropDataFlowOperator>;

fn loan_path_is_precise(loan_path: &LoanPath) -> bool {
    match *loan_path {
        LpVar(_) | LpUpvar(..) => {
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
        LpDowncast(ref lp_base, _) => {
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

impl VariantMatch {
    pub fn ty_and_span(&self, tcx: &ty::ctxt) -> (ty::t, Span) {
        match tcx.map.find(self.id) {
            Some(ast_map::NodePat(pat)) => (ty::pat_ty(tcx, &*pat), pat.span),
            r => tcx.sess.bug(format!("{:?} maps to {:?}, not Pat", self, r).as_slice())
        }
    }
    pub fn ty(&self, tcx: &ty::ctxt) -> ty::t {
        self.ty_and_span(tcx).val0()
    }
    pub fn to_string(&self, move_data: &MoveData, tcx: &ty::ctxt) -> String {
        format!("VariantMatch{:s} path: {}, id: {} {:s}",
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
            variant_matches: RefCell::new(Vec::new()),
            assignee_ids: RefCell::new(HashSet::new()),
            fragments: RefCell::new(Vec::new()),
            nonfragments: RefCell::new(Vec::new()),
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

    /// Returns true iff `index` itself cannot be directly split into
    /// child fragments.  This means it is an atomic value (like a
    /// pointer or an integer), or it a non-downcasted enum (and so we
    /// can only split off subparts when we narrow it to a particular
    /// variant), or it is a struct whose fields are never accessed in
    /// the function being compiled.
    fn path_is_leaf(&self, index: MovePathIndex, _tcx: &ty::ctxt) -> bool {

        let first_child = self.path_first_child(index);
        if first_child == InvalidMovePathIndex {
            true
        } else {
            match *self.path_loan_path(first_child) {
                LpDowncast(..) => true,
                LpExtend(..) => false, // FIXME
                LpVar(..) | LpUpvar(..) => false,
            }
        }
    }

    /// Returns true iff `index` represents downcast to an enum variant (i.e. LpDowncast).
    fn path_is_downcast_to_variant(&self, index: MovePathIndex) -> bool {
        match *self.path_loan_path(index) {
            LpDowncast(..) => true,
            _ => false,
        }
    }

    /// Returns the index of first child, or `InvalidMovePathIndex` if
    /// `index` is leaf.
    fn path_first_child(&self, index: MovePathIndex) -> MovePathIndex {
        self.paths.borrow().get(index.get()).first_child
    }

    /// Returns index for next sibling, or `InvalidMovePathIndex` if
    /// `index` has no remaining siblings in the list.  (The head of
    /// the list is the parent's first child; see `path_first_child`).
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

    fn move_path(&self,
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

            LpDowncast(ref base, _) |
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
                    LpDowncast(ref b, _) => {
                        self.add_existing_base_paths(b, result);
                    }
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

        let path_index = self.move_path(tcx, lp.clone());
        let move_index = MoveIndex(self.moves.borrow().len());

        self.nonfragments.borrow_mut().push(path_index);

        let next_move = self.path_first_move(path_index);
        self.set_path_first_move(path_index, move_index);

        self.moves.borrow_mut().push(Move {
            path: path_index,
            id: id,
            kind: kind,
            next_move: next_move
        });

        self.add_fragment_siblings(tcx, lp, id);
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

        self.nonfragments.borrow_mut().push(path_index);

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

    pub fn add_variant_match(&self,
                         tcx: &ty::ctxt,
                         lp: Rc<LoanPath>,
                         pattern_id: ast::NodeId,
                         base_lp: Rc<LoanPath>) {
        /*!
         * Adds a new record for an match of `base_lp`, downcast to
         * variant `lp`, that occurs at location `pattern_id`.  (One
         * should be able to recover teh span info from the
         * `pattern_id` and the ast_map, I think.)
         */
        debug!("add_variant_match(lp={}, pattern_id={:?})",
               lp.repr(tcx), pattern_id);

        let path_index = self.move_path(tcx, lp.clone());
        let base_path_index = self.move_path(tcx, base_lp.clone());

        self.nonfragments.borrow_mut().push(path_index);
        let variant_match = VariantMatch {
            path: path_index,
            base_path: base_path_index,
            id: pattern_id,
        };

        self.variant_matches.borrow_mut().push(variant_match);
    }

    fn add_fragment_siblings(&self,
                             tcx: &ty::ctxt,
                             lp: Rc<LoanPath>,
                             origin_id: ast::NodeId) {
        /*! Adds all of the precisely-tracked siblings of `lp` as
         * potential move paths of interest. For example, if `lp`
         * represents `s.x.j`, then adds moves paths for `s.x.i` and
         * `s.x.k`, the siblings of `s.x.j`.
         */
        debug!("add_fragment_siblings(lp={}, origin_id={})",
               lp.repr(tcx), origin_id);

        match *lp {
            LpVar(_) | LpUpvar(..) => {} // Local variables have no siblings.

            LpDowncast(..) => {} // an enum variant (on its own) has no siblings.

            // *LV for OwnedPtr consumes the contents of the box (at
            // least when it is non-copy...), so propagate inward.
            LpExtend(ref loan_parent, _, LpDeref(mc::OwnedPtr)) => {
                let msg =
                    format!("add_fragment_siblings encountered \
                            LpExtend(.., OwnedPtr): {}; recursing down.",
                            lp.repr(tcx));
                tcx.sess.opt_span_warn(tcx.map.opt_span(origin_id),
                                       msg.as_slice());
                self.add_fragment_siblings(tcx, loan_parent.clone(), origin_id);
            }

            // *LV has no siblings
            LpExtend(_, _, LpDeref(_)) => {}

            // LV[j] is not tracked precisely
            LpExtend(_, _, LpInterior(mc::InteriorElement(_))) => {}

            // field access LV.x and tuple access LV#k are the cases
            // we are interested in
            LpExtend(ref loan_parent, mc,
                     LpInterior(mc::InteriorField(ref field_name))) => {
                let enum_variant_info = match **loan_parent {
                    LpDowncast(ref loan_parent_2, variant_def_id) =>
                        Some((variant_def_id, loan_parent_2.clone())),
                    LpExtend(..) | LpVar(..) | LpUpvar(..) =>
                        None,
                };
                self.add_fragment_siblings_for_extension(
                    tcx, loan_parent, mc, field_name, &lp, origin_id, enum_variant_info);
            }
        }
    }

    fn add_fragment_siblings_for_extension(&self,
                                           tcx: &ty::ctxt,
                                           parent_lp: &Rc<LoanPath>,
                                           mc: mc::MutabilityCategory,
                                           origin_field_name: &mc::FieldName,
                                           origin_lp: &Rc<LoanPath>,
                                           origin_id: ast::NodeId,
                                           enum_variant_info: Option<(ast::DefId, Rc<LoanPath>)>) {
        /*! We have determined that `origin_lp` destructures to
         * LpExtend(parent, original_field_name). Based on this,
         * add move paths for all of the siblings of `origin_lp`.
         */
        let parent_ty = parent_lp.to_type(tcx);

        let add_fragment_sibling = |field_name, _field_type| {
            self.add_fragment_sibling(
                tcx, parent_lp.clone(), mc, field_name, origin_lp);
        };

        match (&ty::get(parent_ty).sty, enum_variant_info) {
            (&ty::ty_tup(ref v), None) => {
                let tuple_idx = match *origin_field_name {
                    mc::PositionalField(tuple_idx) => tuple_idx,
                    mc::NamedField(_) =>
                        fail!("tuple type {} should not have named fields.",
                              parent_ty.repr(tcx)),
                };
                let tuple_len = v.len();
                for i in range(0, tuple_len) {
                    if i == tuple_idx { continue }
                    let field_type =
                        // v[i];
                        ();
                    let field_name = mc::PositionalField(i);
                    add_fragment_sibling(field_name, field_type);
                }
            }

            (&ty::ty_struct(def_id, ref _substs), None) => {
                let fields = ty::lookup_struct_fields(tcx, def_id);
                match *origin_field_name {
                    mc::NamedField(ast_name) => {
                        for f in fields.iter() {
                            if f.name == ast_name {
                                continue;
                            }
                            let field_name = mc::NamedField(f.name);
                            let field_type = ();
                            add_fragment_sibling(field_name, field_type);
                        }
                    }
                    mc::PositionalField(tuple_idx) => {
                        for (i, _f) in fields.iter().enumerate() {
                            if i == tuple_idx {
                                continue
                            }
                            let field_name = mc::PositionalField(i);
                            let field_type = ();
                            add_fragment_sibling(field_name, field_type);
                        }
                    }
                }
            }

            (&ty::ty_enum(enum_def_id, ref substs), ref enum_variant_info) => {
                let variant_info = {
                    let mut variants = ty::substd_enum_variants(tcx, enum_def_id, substs);
                    match *enum_variant_info {
                        Some((variant_def_id, ref _lp2)) =>
                            variants.iter()
                            .find(|variant| variant.id == variant_def_id)
                            .expect("enum_variant_with_id(): no variant exists with that ID")
                            .clone(),
                        None => {
                            assert!(variants.len() == 1);
                            variants.pop().unwrap()
                        }
                    }
                };
                match *origin_field_name {
                    mc::NamedField(ast_name) => {
                        let variant_arg_names = variant_info.arg_names.as_ref().unwrap();
                        let variant_arg_types = &variant_info.args;
                        for (variant_arg_ident, _variant_arg_ty) in variant_arg_names.iter().zip(variant_arg_types.iter()) {
                            if variant_arg_ident.name == ast_name {
                                continue;
                            }
                            let field_name = mc::NamedField(variant_arg_ident.name);
                            let field_type = ();
                            add_fragment_sibling(field_name, field_type);
                        }
                    }
                    mc::PositionalField(tuple_idx) => {
                        let variant_arg_types = &variant_info.args;
                        for (i, _variant_arg_ty) in variant_arg_types.iter().enumerate() {
                            if tuple_idx == i {
                                continue;
                            }
                            let field_name = mc::PositionalField(i);
                            let field_type = ();
                            add_fragment_sibling(field_name, field_type);
                        }
                    }
                }
            }

            ref sty_and_variant_info => {
                let msg = format!("type {} ({:?}) is not fragmentable",
                                  parent_ty.repr(tcx), sty_and_variant_info);
                tcx.sess.opt_span_bug(tcx.map.opt_span(origin_id),
                                      msg.as_slice())
            }
        }
    }

    fn add_fragment_sibling(&self,
                            tcx: &ty::ctxt,
                            parent: Rc<LoanPath>,
                            mc: mc::MutabilityCategory,
                            new_field_name: mc::FieldName,
                            origin_lp: &Rc<LoanPath>) -> MovePathIndex {
        /*! Adds the single sibling `LpExtend(parent, new_field_name)`
         * of `origin_lp` (the original loan-path).
         */
        let loan_path_elem = LpInterior(mc::InteriorField(new_field_name));
        let lp : LoanPath = LpExtend(parent, mc, loan_path_elem);
        debug!("add_fragment_sibling(lp={}, origin_lp={})",
               lp.repr(tcx), origin_lp.repr(tcx));
        let mp = self.move_path(tcx, Rc::new(lp));

        // Do not worry about checking for duplicates here; if
        // necessary, we will sort and dedup after all are added.
        self.fragments.borrow_mut().push(mp);

        mp
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

        {
            let mut nonfragments = {
                let mut nonfragments = self.nonfragments.borrow_mut();
                nonfragments.sort_by(|a, b| a.get().cmp(&b.get()));
                nonfragments.dedup();
                nonfragments
            };
            let mut fragments = {
                let mut maybe_fragments = self.fragments.borrow_mut();
                maybe_fragments.sort_by(|a, b| a.get().cmp(&b.get()));
                maybe_fragments.dedup();

                // FIXME: why does rustc say that the below code means
                // `nonfragments` must be declared mut?  Potential
                // fallout from recent closure changes?
                maybe_fragments.retain(|f| !nonfragments.contains(f));

                maybe_fragments
            };

            // See FIXME above: being forced to declare `nonfragments` as mut
            for (i, &nf) in nonfragments.iter().enumerate() {
                let lp = self.path_loan_path(nf);
                debug!("add_gen_kills nonfragment {:u}: {:s}", i, lp.repr(tcx));
            }

            // See FIXME above: being forced to declare `fragments` as mut
            for (i, &f) in fragments.iter().enumerate() {
                let lp = self.path_loan_path(f);
                debug!("add_gen_kills fragment {:u}: {:s}", i, lp.repr(tcx));
            }
        }

        for (i, move) in self.moves.borrow().iter().enumerate() {
            dfcx_moves.add_gen(move.id, i);
            debug!("remove_drop_obligations move {}", move.to_string(self, tcx));
            self.remove_drop_obligations(tcx, move, dfcx_needs_drop);
        }

        for variant_match in self.variant_matches.borrow().iter() {
            debug!("remove_drop_obligations variant_match {}", variant_match.to_string(self, tcx));
            self.remove_drop_obligations(tcx, variant_match, dfcx_needs_drop);
            debug!("add_drop_obligations variant_match {}", variant_match.to_string(self, tcx));
            self.add_drop_obligations(tcx, variant_match, dfcx_needs_drop);
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
                    let move_path_index =
                        *self.path_map.borrow().get(&path.loan_path);
                    self.kill_moves(move_path_index, kill_id, dfcx_moves);
                    debug!("remove_drop_obligations scope {} {}",
                           kill_id, path.loan_path.repr(tcx));
                    let rm = Removed { where: kill_id, what_path: move_path_index };
                    self.remove_drop_obligations(tcx, &rm, dfcx_needs_drop);
                }
                LpUpvar(ty::UpvarId { var_id: _, closure_expr_id }, _) => {
                    let kill_id = closure_to_block(closure_expr_id, tcx);
                    let move_path_index = *self.path_map.borrow().get(&path.loan_path);
                    self.kill_moves(move_path_index, kill_id, dfcx_moves);
                    debug!("remove_drop_obligations scope {} {}",
                           kill_id, path.loan_path.repr(tcx));
                    let rm = Removed { where: kill_id, what_path: move_path_index };
                    self.remove_drop_obligations(tcx, &rm, dfcx_needs_drop);
                }
                LpDowncast(..) => {} // FIXME: is this right, or should this loop to top?
                LpExtend(..) => {}
            }
        }

        // Kill all assignments when the variable goes out of scope:
        for (assignment_index, assignment) in self.var_assignments.borrow().iter().enumerate() {
            let kill_id = self.path_loan_path(assignment.path).kill_id(tcx);
            dfcx_assign.add_kill(kill_id, assignment_index);
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


    // A digression on needs-drop design.
    //
    // Lets assume we had a pre-existing drop obligation ND = { s.a, s2 }, where:
    // ```
    // struct S { a: A, b: B, c: C }
    // struct A { i: I, j: J, k: K }
    // struct J { x: X, y: Y, z: Z }
    // ```
    // and `s : S` (and `s2 : S` as well).
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
    //
    // For d/d{.j.x}(s.a), S = .j.x and P = s.a:
    //
    // 1. P_0 = s.a      : remove obligation s.a, if present
    //
    // 2. P_1 = s.a.j    : assert obligation s.a.j not present; add
    //                     all needs-drop fields of s.a, then remove s.a.j.
    // 3. P_2 = s.a.j.x  : assert obligation s.a.j.x not present; add
    //                     all needs-drop fields of s.a.j, then remove s.a.j.x.
    //
    // Big Question: Under the kill/gen paradigm, how do I ensure that
    // I only add the bits associated with d/d{.j.x}(s.a) and not the
    // bits associated with d/d{.a.j.x}(s) ?  I.e. the explanation
    // above makes assumptions about computations I will be able to do
    // as part the transfer function, but I need to encode those
    // computations as gen+kill bits.
    //
    // ==> one way to resolve this problem while remaining under the
    //     gen/kill paradigm is to carry-on with a suggestion I made
    //     to Niko a while back, namely to treat the path `s` as a
    //     shorthand for
    //
    //      `{ s.a.i, s.a.j.x, s.a.j.y, s.a.j.z, s.a.k, s.b, s.c }`,
    //
    //     and likewise `s.a` as as shorthand for
    //
    //      `{ s.a.i, s.a.j.x, s.a.j.y, s.a.j.z, s.a.k }`
    //
    //     That is, put these paths through a normalization process that
    //     unrolls them to their leaves (or at least, their leaves with
    //     respect to a given piece of code.
    //
    //     I might even be able to implement this independently of
    //     the other dataflow analyses, since happenstance led me
    //     to make the needs-drop analysis separate from the
    //     loans/moves/assigns analyses.
    //
    // UPDATE: The above is in fact the strategy that Felix went with.
    // The above comment should be revised/shortened to a succinct
    // summary.

    fn path_needs_drop(&self, tcx: &ty::ctxt, move_path_index: MovePathIndex) -> bool {
        //! Returns true iff move_path_index needs drop.
        self.path_loan_path(move_path_index).needs_drop(tcx)
    }

    fn type_moves_by_default(&self, tcx: &ty::ctxt, move_path_index: MovePathIndex) -> bool {
        //! Returns true iff move_path_index needs moves by default.
        let path_type = self.path_loan_path(move_path_index).to_type(tcx);
        ty::type_contents(tcx, path_type).moves_by_default(tcx)
    }

    fn for_each_leaf(&self,
                     tcx: &ty::ctxt,
                     root: MovePathIndex,
                     found_leaf: |MovePathIndex|,
                     _found_variant: |MovePathIndex|) {
        //! Here we normalize a path so that it is unraveled to its
        //! consituent droppable pieces that might be independently
        //! handled by the function being compiled: e.g. `s.a.j`
        //! unravels to `{ s.a.j.x, s.a.j.y, s.a.j.z }` (assuming the
        //! function never moves out any part of those unraveled
        //! elements).
        //!
        //! Note that the callback is only invoked on unraveled leaves
        //! that also need to be dropped.

        let root_lp = self.path_loan_path(root);
        debug!("for_each_leaf(root_lp={:s})", root_lp.repr(tcx));

        if self.path_is_leaf(root, tcx) {
            found_leaf(root);
            return;
        }

        let mut stack = vec![];
        stack.push(root);
        loop {
            let top = match stack.pop() { None => break, Some(elem) => elem };
            assert!(!self.path_is_leaf(top, tcx));
            let mut child = self.path_first_child(top);
            while child != InvalidMovePathIndex {
                {
                    let top_lp = self.path_loan_path(top);
                    let child_lp = self.path_loan_path(child);
                    debug!("for_each_leaf(root_lp={:s}){:s} top_lp={:s} child_lp={:s}",
                           root_lp.repr(tcx),
                           " ".repeat(stack.len()),
                           top_lp.repr(tcx),
                           child_lp.repr(tcx));
                }

                if self.path_is_leaf(child, tcx) {
                    found_leaf(child);
                } else {
                    stack.push(child);
                }

                child = self.path_next_sibling(child);
            }
        }
    }

    fn add_drop_obligations<A:AddNeedsDropArg>(&self,
                                               tcx: &ty::ctxt,
                                               a: &A,
                                               dfcx_needs_drop: &mut NeedsDropDataFlow) {
        let a_id = a.node_id_adding_obligation();
        let a_path = a.path_being_established();

        let add_gen = |move_path_index| {
            if self.path_is_downcast_to_variant(a_path) {
                debug!("add_drop_obligations(a={}) {} is variant on match arm",
                       a.to_string_(self, tcx),
                       self.path_loan_path(move_path_index).repr(tcx));
            }

            if self.path_needs_drop(tcx, move_path_index) {
                debug!("add_drop_obligations(a={}) adds {}",
                       a.to_string_(self, tcx),
                       self.path_loan_path(move_path_index).repr(tcx));
                dfcx_needs_drop.add_gen(a_id, move_path_index.get());
            } else {
                debug!("add_drop_obligations(a={}) skips non-drop {}",
                       a.to_string_(self, tcx),
                       self.path_loan_path(move_path_index).repr(tcx));
            }
        };

        let report_variant = |move_path_index| {
            debug!("add_drop_obligations(a={}) skips variant {}",
                   a.to_string_(self, tcx),
                   self.path_loan_path(move_path_index).repr(tcx));
        };

        self.for_each_leaf(tcx, a_path, add_gen, report_variant);
    }

    fn remove_drop_obligations<A:RemoveNeedsDropArg>(&self,
                                                     tcx: &ty::ctxt,
                                                     a: &A,
                                                     dfcx_needs_drop: &mut NeedsDropDataFlow) {
        //! Kills all of the fragment leaves of path.
        //!
        //! Also kills all parents of path: while we do normalize a
        //! path to its fragment leaves, (e.g. `a.j` to `{a.j.x,
        //! a.j.y, a.j.z}`, an enum variant's path `(b:Variant1).x`
        //! has the parent `b` that is itself considered a "leaf" for
        //! the purposes of tracking drop obligations.

        let id = a.node_id_removing_obligation();
        let path : MovePathIndex = a.path_being_moved();

        let add_kill = |move_path_index| {
            if self.type_moves_by_default(tcx, move_path_index) {
                debug!("remove_drop_obligations(id={}) removes {}",
                       id, self.path_loan_path(move_path_index).repr(tcx));
                dfcx_needs_drop.add_kill(id, move_path_index.get());
            } else {
                debug!("remove_drop_obligations(id={}) skips copyable {}",
                       id, self.path_loan_path(move_path_index).repr(tcx));
            }
        };

        let report_variant = |move_path_index| {
            debug!("remove_drop_obligations(id={}) skips variant {}",
                   id, self.path_loan_path(move_path_index).repr(tcx));
        };

        self.for_each_leaf(tcx, path, add_kill, report_variant);
    }
}

trait AddNeedsDropArg {
    fn node_id_adding_obligation(&self) -> ast::NodeId;
    fn path_being_established(&self) -> MovePathIndex;
    fn to_string_(&self, move_data: &MoveData, tcx: &ty::ctxt) -> String;
}
impl AddNeedsDropArg for Assignment {
    fn node_id_adding_obligation(&self) -> ast::NodeId { self.id }
    fn path_being_established(&self) -> MovePathIndex { self.path }
    fn to_string_(&self, md: &MoveData, tcx: &ty::ctxt) -> String { self.to_string(md, tcx) }
}
impl AddNeedsDropArg for VariantMatch {
    fn node_id_adding_obligation(&self) -> ast::NodeId { self.id }
    fn path_being_established(&self) -> MovePathIndex { self.path }
    fn to_string_(&self, md: &MoveData, tcx: &ty::ctxt) -> String { self.to_string(md, tcx) }
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
impl<'a> RemoveNeedsDropArg for Move {
    fn node_id_removing_obligation(&self) -> ast::NodeId { self.id }
    fn path_being_moved(&self) -> MovePathIndex { self.path }
}
impl<'a> RemoveNeedsDropArg for VariantMatch {
    fn node_id_removing_obligation(&self) -> ast::NodeId { self.id }
    fn path_being_moved(&self) -> MovePathIndex { self.base_path }
}

impl<'a, 'tcx> FlowedMoveData<'a, 'tcx> {
    pub fn new(move_data: MoveData,
               tcx: &'a ty::ctxt<'tcx>,
               cfg: &cfg::CFG,
               id_range: ast_util::IdRange,
               decl: &ast::FnDecl,
               body: &ast::Block)
               -> FlowedMoveData<'a, 'tcx> {
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
        // But of course need to deal with states before we hit the
        // fixed point.  Consider the following while-loop:
        //
        //   `{ let a = box 3; while <cond> { <body> } <rest> }`
        // where <cond> and <body> do not move or drop `a`:
        //
        //                    [let a = box 3;]
        //                      |
        //                      v 1
        //                  [loopback] <--+ 5
        //                      |         |
        //                      v 2       |
        //              +-----[cond]      |
        //              |       |         |
        //              |       v 4       |
        //              |     [body] -----+
        //              v 3
        //            [rest]
        //
        // we need to ensure that the fixed-point solution registers
        // that `a` is needs-drop on all of the above edges.  (Note
        // that choosing logical-and and a false initial value would
        // cause the fixed point solution to falsely claim that `a` is
        // only needs-drop on edge 1, because edge 5 would start as
        // false and then the merge between edge 1 and edge 5 would be
        // logically anded to false on edge 2, and so on.)
        //
        // We could use logical-or here (and a false initial value)
        // like the other analyses.  Or, we can (and do) use
        // logical-and and a true initial value.  For correct code,
        // they will both end with the same fixed point.
        //
        // The reason to use logical-and instead of logical-or is
        // error reporting.  In particular, we start with an
        // assumption.
        //
        // ASSUMPTION: When there is a discrepancy between the set of
        // drop-obligations for two paths at a merge point, we assume
        // for the purposes of error reporting that the error was that
        // the user forgot to include a drop of the resource, *not*
        // that the user intended to re-establish the resource on the
        // path where it had been dropped.
        //
        // Consider the following example:
        //
        //                       [let a = box 3;]             
        //                             +                      
        //                             |                      
        //                             v                      
        //                    +---+[cond 1]+--+               
        //    (a needs drop)  |               | (a needs drop)
        //                    v               |               
        //             +-+[cond 2]+-+         |               
        //             |            |         |               
        //             v            v         v               
        //     [no use of a]   [consume a]   [consume a]      
        //                +         +         |               
        // (a needs drop) |         |  ()     | ()            
        //                v         v         |               
        //              [merge point 1]       |               
        //                    +               |               
        //                (*) |               |               
        //                    +---------+     |               
        //                              |     |               
        //                              v     v               
        //                          [merge point 2]           
        //
        // At `[merge point 1]`, we obviously report a discrepancy
        // between the two incoming paths.  The question: What do we
        // want the set of drop obligations to be at the exit of
        // `[merge point 1]`, where the `(*)` is marked.  There are
        // two possible choices for `(*)`: `()`, and `(a needs drop)`.
        //
        // Choosing `(a needs drop)` corresponds to an assumption that
        // on the path where `a` was dropped, the programmer probably
        // meant to re-establish `a`.  To get this choice, one would
        // use logical-or here.
        //
        // Choosing `()` corresponds to an assumption that on the path
        // where `a` was not dropped, the programmer probably meant to
        // drop it.  To get this choice, we use logical-and here.
        //
        // Each choice for `(*)` also has implications for when
        // check_drops considers `[merge point 2]`: Choosing `()`
        // means that nothing is reported for `[merge point 2]`, since
        // the two incoming paths have the same set of drop
        // obligations.  Choosing `(a needs drop)` means that we get a
        // similar error report to the one for `[merge point 1]`,
        // which may be frustrating to the programmer who already
        // probably saw that they would need to add the drop of `a` on
        // the far left path.
        //
        // (One could argue that the above example is artificial,
        // since a small alteration of the graph above has a path on
        // the far right-hand side that does not consume `a`, and in
        // that situation, choosing `(a needs drop)` for `(*)` will
        // produce fewer error messages.  However, we are *not*
        // selecting logical-and over logical-or solely based on some
        // expectation of the number of error messages encountered.
        // Instead, it is based on our starting assumption: if in
        // example above the far right path is missing a drop of a,
        // then by our assumption, we *should* issue two error
        // reports, since there are *two* places where the programmer
        // needs to add calls to drop: the far left-hand path, and the
        // far right-hand path.)

        succ & pred
    }
}

impl DataFlowOperator for NeedsDropDataFlowOperator {
    #[inline]
    fn initial_value(&self) -> bool {
        // For non-entry nodes, assume paths need dropping until
        // proven otherwise.
        //
        // See extensive discussion in impl BitwiseOperator for
        // NeedsDropDataFlowOperator.
        true
    }

    #[inline]
    fn entry_initial_value(&self) -> bool {
        false
    }
}
