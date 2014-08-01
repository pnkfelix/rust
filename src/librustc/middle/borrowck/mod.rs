// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! See doc.rs for a thorough explanation of the borrow checker */

#![allow(non_camel_case_types)]

use middle::cfg;
use middle::dataflow::DataFlowContext;
use middle::dataflow::BitwiseOperator;
use middle::dataflow::DataFlowOperator;
use middle::def;
use middle::expr_use_visitor as euv;
use middle::mem_categorization as mc;
use middle::ty;
use middle::subst::Subst;
use util::ppaux::{note_and_explain_region, Repr, UserString};

use std::cell::{Cell};
use std::rc::Rc;
use std::gc::{Gc, GC};
use std::string::String;
use syntax::ast;
use syntax::ast_map;
use syntax::ast_map::blocks::{FnLikeNode, FnParts};
use syntax::ast_util;
use syntax::codemap::Span;
use syntax::parse::token;
use syntax::visit;
use syntax::visit::{Visitor, FnKind};
use syntax::ast::{FnDecl, Block, NodeId};

macro_rules! if_ok(
    ($inp: expr) => (
        match $inp {
            Ok(v) => { v }
            Err(e) => { return Err(e); }
        }
    )
)

pub mod doc;

pub mod check_loans;

pub mod gather_loans;

pub mod graphviz;

pub mod move_data;

pub mod check_drops;

#[deriving(Clone)]
pub struct LoanDataFlowOperator;

pub type LoanDataFlow<'a, 'tcx> = DataFlowContext<'a, 'tcx, LoanDataFlowOperator>;

impl<'a, 'tcx> Visitor<()> for BorrowckCtxt<'a, 'tcx> {
    fn visit_fn(&mut self, fk: &FnKind, fd: &FnDecl,
                b: &Block, s: Span, n: NodeId, _: ()) {
        borrowck_fn(self, fk, fd, b, s, n);
    }

    fn visit_item(&mut self, item: &ast::Item, _: ()) {
        borrowck_item(self, item);
    }
}

pub fn check_crate(tcx: &ty::ctxt,
                   krate: &ast::Crate) {
    let mut bccx = BorrowckCtxt {
        tcx: tcx,
        stats: box(GC) BorrowStats {
            loaned_paths_same: Cell::new(0),
            loaned_paths_imm: Cell::new(0),
            stable_paths: Cell::new(0),
            guaranteed_paths: Cell::new(0),
        }
    };

    visit::walk_crate(&mut bccx, krate, ());

    if tcx.sess.borrowck_stats() {
        println!("--- borrowck stats ---");
        println!("paths requiring guarantees: {}",
                 bccx.stats.guaranteed_paths.get());
        println!("paths requiring loans     : {}",
                 make_stat(&bccx, bccx.stats.loaned_paths_same.get()));
        println!("paths requiring imm loans : {}",
                 make_stat(&bccx, bccx.stats.loaned_paths_imm.get()));
        println!("stable paths              : {}",
                 make_stat(&bccx, bccx.stats.stable_paths.get()));
    }

    fn make_stat(bccx: &BorrowckCtxt, stat: uint) -> String {
        let total = bccx.stats.guaranteed_paths.get() as f64;
        let perc = if total == 0.0 { 0.0 } else { stat as f64 * 100.0 / total };
        format!("{} ({:.0f}%)", stat, perc)
    }
}

fn borrowck_item(this: &mut BorrowckCtxt, item: &ast::Item) {
    // Gather loans for items. Note that we don't need
    // to check loans for single expressions. The check
    // loan step is intended for things that have a data
    // flow dependent conditions.
    match item.node {
        ast::ItemStatic(_, _, ex) => {
            gather_loans::gather_loans_in_static_initializer(this, &*ex);
        }
        _ => {
            visit::walk_item(this, item, ());
        }
    }
}

/// Collection of conclusions determined via borrow checker analyses.
pub struct AnalysisData<'a, 'tcx: 'a> {
    pub all_loans: Vec<Loan>,
    pub loans: DataFlowContext<'a, 'tcx, LoanDataFlowOperator>,
    pub move_data: move_data::FlowedMoveData<'a, 'tcx>,
}

fn borrowck_fn(this: &mut BorrowckCtxt,
               fk: &FnKind,
               decl: &ast::FnDecl,
               body: &ast::Block,
               sp: Span,
               id: ast::NodeId) {
    debug!("borrowck_fn(id={})", id);
    let cfg = cfg::CFG::new(this.tcx, body);
    let AnalysisData { all_loans,
                       loans: loan_dfcx,
                       move_data:flowed_moves } =
        build_borrowck_dataflow_data(this, fk, decl, &cfg, body, sp, id);

    check_drops::check_drops(this, &flowed_moves, &cfg, decl, body);

    check_loans::check_loans(this, &loan_dfcx, flowed_moves,
                             all_loans.as_slice(), decl, body);

    visit::walk_fn(this, fk, decl, body, sp, ());
}

fn build_borrowck_dataflow_data<'a, 'tcx>(this: &mut BorrowckCtxt<'a, 'tcx>,
                                          fk: &FnKind,
                                          decl: &ast::FnDecl,
                                          cfg: &cfg::CFG,
                                          body: &ast::Block,
                                          sp: Span,
                                          id: ast::NodeId) -> AnalysisData<'a, 'tcx> {
    // Check the body of fn items.
    let id_range = ast_util::compute_id_range_for_fn_body(fk, decl, body, sp, id);
    let (all_loans, move_data) =
        gather_loans::gather_loans_in_fn(this, decl, body);

    let mut loan_dfcx =
        DataFlowContext::new(this.tcx,
                             "borrowck",
                             Some(decl),
                             cfg,
                             LoanDataFlowOperator,
                             id_range,
                             all_loans.len());
    for (loan_idx, loan) in all_loans.iter().enumerate() {
        loan_dfcx.add_gen(loan.gen_scope, loan_idx);
        loan_dfcx.add_kill(loan.kill_scope, loan_idx);
    }
    loan_dfcx.add_kills_from_flow_exits(cfg);
    loan_dfcx.propagate(cfg, body);

    let flowed_moves = move_data::FlowedMoveData::new(move_data,
                                                      this.tcx,
                                                      cfg,
                                                      id_range,
                                                      decl,
                                                      body);

    AnalysisData { all_loans: all_loans,
                   loans: loan_dfcx,
                   move_data:flowed_moves }
}

/// This and a `ty::ctxt` is all you need to run the dataflow analyses
/// used in the borrow checker.
pub struct FnPartsWithCFG<'a> {
    pub fn_parts: FnParts<'a>,
    pub cfg:  &'a cfg::CFG,
}

impl<'a> FnPartsWithCFG<'a> {
    pub fn from_fn_like(f: &'a FnLikeNode,
                        g: &'a cfg::CFG) -> FnPartsWithCFG<'a> {
        FnPartsWithCFG { fn_parts: f.to_fn_parts(), cfg: g }
    }
}

/// Accessor for introspective clients inspecting `AnalysisData` and
/// the `BorrowckCtxt` itself , e.g. the flowgraph visualizer.
pub fn build_borrowck_dataflow_data_for_fn<'a, 'tcx>(
    tcx: &'a ty::ctxt<'tcx>,
    input: FnPartsWithCFG<'a>) -> (BorrowckCtxt<'a, 'tcx>, AnalysisData<'a, 'tcx>) {

    let mut bccx = BorrowckCtxt {
        tcx: tcx,
        stats: box(GC) BorrowStats {
            loaned_paths_same: Cell::new(0),
            loaned_paths_imm: Cell::new(0),
            stable_paths: Cell::new(0),
            guaranteed_paths: Cell::new(0),
        }
    };

    let p = input.fn_parts;

    let dataflow_data = build_borrowck_dataflow_data(&mut bccx,
                                                     &p.kind,
                                                     &*p.decl,
                                                     input.cfg,
                                                     &*p.body,
                                                     p.span,
                                                     p.id);

    (bccx, dataflow_data)
}

// ----------------------------------------------------------------------
// Type definitions

pub struct BorrowckCtxt<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,

    // Statistics:
    stats: Gc<BorrowStats>,
}

pub struct BorrowStats {
    loaned_paths_same: Cell<uint>,
    loaned_paths_imm: Cell<uint>,
    stable_paths: Cell<uint>,
    guaranteed_paths: Cell<uint>,
}

pub type BckResult<T> = Result<T, BckError>;

#[deriving(PartialEq)]
pub enum PartialTotal {
    Partial,   // Loan affects some portion
    Total      // Loan affects entire path
}

///////////////////////////////////////////////////////////////////////////
// Loans and loan paths

/// Record of a loan that was issued.
pub struct Loan {
    index: uint,
    loan_path: Rc<LoanPath>,
    kind: ty::BorrowKind,
    restricted_paths: Vec<Rc<LoanPath>>,
    gen_scope: ast::NodeId,
    kill_scope: ast::NodeId,
    span: Span,
    cause: euv::LoanCause,
}

impl Loan {
    pub fn loan_path(&self) -> Rc<LoanPath> {
        self.loan_path.clone()
    }
}

#[deriving(PartialEq, Eq, Hash)]
pub enum CaptureKind { CaptureByVal, CaptureByRef }

#[deriving(PartialEq, Eq, Hash)]
pub enum LoanPath {
    LpVar(ast::NodeId),                   // `x` in doc.rs
    LpUpvar(ty::UpvarId, CaptureKind),    // `x` captured by-value into closure
    LpDowncast(Rc<LoanPath>, ast::DefId), // `x` downcast to particular enum variant
    LpExtend(Rc<LoanPath>, mc::MutabilityCategory, LoanPathElem),
}

impl LoanPath {
    fn kill_id(&self, tcx: &ty::ctxt) -> ast::NodeId {
        //! Returns the lifetime of the local variable that forms the base of this path.
        match *self {
            LpVar(id) =>
                tcx.region_maps.var_scope(id),
            LpUpvar(ty::UpvarId { var_id: _, closure_expr_id }, _) => 
                closure_to_block(closure_expr_id, tcx),
            LpDowncast(ref base_lp, _) | LpExtend(ref base_lp, _, _) =>
                base_lp.kill_id(tcx),
        }
    }

    fn to_type(&self, tcx: &ty::ctxt) -> ty::t {
        use Element = middle::mem_categorization::InteriorElement;
        use Field = middle::mem_categorization::InteriorField;

        debug!("lp.to_type() for lp={:s}", self.repr(tcx));
        let opt_ty = match *self {
            LpUpvar(ty::UpvarId { var_id: id, closure_expr_id: _ }, capture) =>
                ty::node_id_to_type_opt(tcx, id).map(|t| {
                    match capture {
                        CaptureByVal => t,
                        CaptureByRef =>
                            ty::mk_ptr(tcx, ty::mt{ty: t,
                                                   // making up immut here.
                                                   // Hopefully won't matter.
                                                   mutbl: ast::MutImmutable}),
                    }}),

            LpVar(id) => ty::node_id_to_type_opt(tcx, id),

            // treat the downcasted enum as having the enum's type;
            // extracting the particular types within the variant is
            // handled by `LpExtend` cases.
            LpDowncast(ref lp, _variant_did) => Some(lp.to_type(tcx)),

            LpExtend(ref lp, _mc, ref loan_path_elem) => {
                let (opt_variant_did, lp) = match **lp {
                    LpDowncast(ref sub_lp, variant_did) =>
                        (Some(variant_did), sub_lp),
                    LpVar(..) | LpUpvar(..) | LpExtend(..) =>
                        (None, lp)
                };

                let t = lp.to_type(tcx);
                let t_sty = &ty::get(t).sty;

                match (loan_path_elem, t_sty) {
                    (&LpDeref(_), &ty::ty_ptr(ty::mt{ty: t, ..})) |
                    (&LpDeref(_), &ty::ty_rptr(_, ty::mt{ty: t, ..})) |
                    (&LpDeref(_), &ty::ty_box(t)) |
                    (&LpDeref(_), &ty::ty_uniq(t)) => Some(t),

                    (&LpInterior(Field(mc::NamedField(ast_name))),
                     _) => ty::named_element_ty(tcx, t, ast_name, opt_variant_did),

                    (&LpInterior(Field(mc::PositionalField(idx))),
                     _) => ty::positional_element_ty(tcx, t, idx, opt_variant_did),

                    // (Deliberately not using ty::array_element_ty
                    // here, because that assumes r-value context and
                    // returns deref'ed elem type, but loan structure
                    // separates element-access from deref.)
                    (&LpInterior(Element(_)), &ty::ty_str) =>
                        Some(ty::mk_ptr(tcx, ty::mt{ty: ty::mk_u8(),
                                                    mutbl: ast::MutImmutable})),
                    (&LpInterior(Element(_)), &ty::ty_vec(mt, _len)) =>
                        Some(ty::mk_ptr(tcx, mt)),

                    (lp_elem, _) => {
                        let id = self.kill_scope(tcx);
                        let msg =
                            format!("Unexpected combination of LpExtend \
                                     with LoanPathElem={:?} and base t = {}",
                                    lp_elem, t.repr(tcx));
                        let opt_span = tcx.map.opt_span(id);
                        tcx.sess.opt_span_bug(opt_span, msg.as_slice())
                    }
                }
            }
        };
        let t = opt_ty.unwrap_or_else(|| {
            let id = self.kill_scope(tcx);
            let msg = format!("no type found for lp={:s}", self.repr(tcx));
            let opt_span = tcx.map.opt_span(id);
            tcx.sess.opt_span_bug(opt_span, msg.as_slice());
        });
        debug!("lp.to_type() for lp={:s} returns t={:s}",
               self.repr(tcx), t.repr(tcx));
        t
    }

    fn needs_drop(&self, tcx: &ty::ctxt) -> bool {
        //! Returns true if this loan path needs drop glue.  I.e.,
        //! does introducing this loan path as a binding introduce a
        //! new drop obligation.

        debug!("needs_drop(tcx) self={}", self.repr(tcx));

        match *self {
            LpVar(_) | LpUpvar(..) =>
                // Variables are the easiest case: just use their
                // types to determine wwhether they introduce a drop
                // obligation when assigned.  (FSK well, at the
                // *moment* they are easy; we may put in
                // flow-sensitivity in some form.  Or maybe not, we
                // will see.)
                self.to_type(tcx).needs_drop_call(tcx),

            LpExtend(_, _, LpDeref(_)) =>
                // A path through a `&` or `&mut` reference cannot
                // introduce a drop obligation; e.g. the assignment
                // `*p = box 3u` installs a pointer elsewhere that is
                // the responsibility of someone else (e.g. a caller).
                false,

            LpExtend(ref base_lp, _cat, LpInterior(_)) =>
                // 1. Ensure base_lp does not nullify the drop
                //    obligation (e.g. if it is through a LpDeref,
                //    such as an example like `*x.p = box 3u` (which
                //    in the source code may look like `x.p = box 3u`
                //    due to autoderef).
                base_lp.needs_drop(tcx) &&

                // 2. Even if the base_lp needs drop, this particular
                //    field might not.  E.g. for `x.q = 3u`, `x` may
                //    itself introduce a drop obligation, but the type
                //    of `q` means that that particular field does not
                //    affect dropping.
                self.to_type(tcx).needs_drop_call(tcx),

            LpDowncast(ref lp, def_id) => self.enum_variant_needs_drop(tcx, lp, def_id),
        }
    }

    fn enum_variant_needs_drop(&self,
                               tcx: &ty::ctxt,
                               lp: &Rc<LoanPath>,
                               variant_def_id: ast::DefId) -> bool {
        //! Handle a particular enum variant as a special case, since
        //! the type of an enum variant, like `None` has type
        //! `Option<T>`, can indicate that it needs-drop, even though
        //! that particular variant does not introduce a
        //! drop-obligation.

        let lp_type = lp.to_type(tcx);
        match ty::get(lp_type).sty {
            ty::ty_enum(enum_def_id, ref substs) => {
                let variant_info = ty::enum_variant_with_id(tcx, enum_def_id, variant_def_id);
                let type_contents = ty::TypeContents::union(
                    variant_info.args.as_slice(),
                    |arg_ty| {
                        let arg_ty_subst = arg_ty.subst(tcx, substs);
                        debug!("needs_drop(tcx) self={} arg_ty={:s} arg_ty_subst={:s}",
                               self.repr(tcx), arg_ty.repr(tcx), arg_ty_subst.repr(tcx));
                        ty::type_contents(tcx, arg_ty_subst)
                    });

                type_contents.needs_drop_call(tcx)
            }
            _ => fail!("encountered LpDowncast on non-enum base type."),
        }
    }
}

trait NeedsDropCallArg {
    fn needs_drop_call(&self, tcx: &ty::ctxt) -> bool;
}
impl NeedsDropCallArg for ty::TypeContents {
    fn needs_drop_call(&self, tcx: &ty::ctxt) -> bool {
        // self.needs_drop(tcx)
        self.moves_by_default(tcx)
    }
}
impl NeedsDropCallArg for ty::t {
    fn needs_drop_call(&self, tcx: &ty::ctxt) -> bool {
        ty::type_contents(tcx, *self).needs_drop_call(tcx)
    }
}

#[deriving(PartialEq, Eq, Hash)]
pub enum LoanPathElem {
    LpDeref(mc::PointerKind),    // `*LV` in doc.rs
    LpInterior(mc::InteriorKind) // `LV.f` in doc.rs
    // LpInterior(mc::InteriorKind, Box<InteriorInfo>) // `LV.f` in doc.rs
}

pub enum InteriorInfo {
    StructInterior(ty::t),
    TupleIndexInterior(Vec<ty::t>),
    EnumVariantInterior(ty::VariantInfo),
}

pub fn closure_to_block(closure_id: ast::NodeId,
                    tcx: &ty::ctxt) -> ast::NodeId {
    match tcx.map.get(closure_id) {
        ast_map::NodeExpr(expr) => match expr.node {
            ast::ExprProc(_, block) |
            ast::ExprFnBlock(_, _, block) |
            ast::ExprUnboxedFn(_, _, _, block) => { block.id }
            _ => fail!("encountered non-closure id: {}", closure_id)
        },
        _ => fail!("encountered non-expr id: {}", closure_id)
    }
}

impl LoanPath {
    pub fn kill_scope(&self, tcx: &ty::ctxt) -> ast::NodeId {
        match *self {
            LpVar(local_id) => tcx.region_maps.var_scope(local_id),
            LpUpvar(upvar_id, _) =>
                closure_to_block(upvar_id.closure_expr_id, tcx),
            LpDowncast(ref base, _) |
            LpExtend(ref base, _, _) => base.kill_scope(tcx),
        }
    }
}

pub fn opt_loan_path(cmt: &mc::cmt, tcx: &ty::ctxt) -> Option<Rc<LoanPath>> {
    //! Computes the `LoanPath` (if any) for a `cmt`.
    //! Note that this logic is somewhat duplicated in
    //! the method `compute()` found in `gather_loans::restrictions`,
    //! which allows it to share common loan path pieces as it
    //! traverses the CMT.

    debug!("opt_loan_path(cmt={})", cmt.repr(tcx));

    let ret = match cmt.cat {
        mc::cat_rvalue(..) |
        mc::cat_static_item |
        mc::cat_copied_upvar(mc::CopiedUpvar { onceness: ast::Many, .. }) => {
            None
        }

        mc::cat_local(id) |
        mc::cat_arg(id) => {
            Some(Rc::new(LpVar(id)))
        }

        mc::cat_upvar(ty::UpvarId {var_id: id, closure_expr_id: proc_id}, _) => {
            let upvar_id = ty::UpvarId{ var_id: id, closure_expr_id: proc_id };
            Some(Rc::new(LpUpvar(upvar_id, CaptureByRef)))
        }
        mc::cat_copied_upvar(mc::CopiedUpvar { upvar_id: id,
                                               onceness: _,
                                               capturing_proc: proc_id }) => {
            let upvar_id = ty::UpvarId{ var_id: id, closure_expr_id: proc_id };
            Some(Rc::new(LpUpvar(upvar_id, CaptureByVal)))
        }

        mc::cat_deref(ref cmt_base, _, pk) => {
            opt_loan_path(cmt_base, tcx).map(|lp| {
                let lp : LoanPath =
                    LpExtend(lp, cmt.mutbl, LpDeref(pk)); 
                Rc::new(lp)
            })
        }

        mc::cat_interior(ref cmt_base, ik) => {
            opt_loan_path(cmt_base, tcx).map(|lp| {
                let lp : LoanPath =
                    LpExtend(lp, cmt.mutbl, LpInterior(ik));
                Rc::new(lp)
            })
        }

        mc::cat_downcast(ref cmt_base, variant_def_id) =>
            opt_loan_path(cmt_base, tcx)
            .map(|lp| {
                debug!("opt_loan_path cat_downcast \
                        cmt.ty={} ({:?}) \
                        cmt_base.ty={} ({:?})",
                       cmt.ty.repr(tcx), cmt.ty,
                       cmt_base.ty.repr(tcx), cmt_base.ty);
                Rc::new(LpDowncast(lp, variant_def_id))
            }),
        mc::cat_discr(ref cmt_base, _) => opt_loan_path(cmt_base, tcx),
    };

    debug!("opt_loan_path(cmt={}) => {}", cmt.repr(tcx), ret.repr(tcx));

    ret
}

///////////////////////////////////////////////////////////////////////////
// Errors

// Errors that can occur
#[deriving(PartialEq)]
pub enum bckerr_code {
    err_mutbl,
    err_out_of_scope(ty::Region, ty::Region), // superscope, subscope
    err_borrowed_pointer_too_short(ty::Region, ty::Region), // loan, ptr
}

// Combination of an error code and the categorization of the expression
// that caused it
#[deriving(PartialEq)]
pub struct BckError {
    span: Span,
    cause: euv::LoanCause,
    cmt: mc::cmt,
    code: bckerr_code
}

pub enum AliasableViolationKind {
    MutabilityViolation,
    BorrowViolation(euv::LoanCause)
}

pub enum MovedValueUseKind {
    MovedInUse,
    MovedInCapture,
}

///////////////////////////////////////////////////////////////////////////
// Misc

impl<'a, 'tcx> BorrowckCtxt<'a, 'tcx> {
    pub fn is_subregion_of(&self, r_sub: ty::Region, r_sup: ty::Region)
                           -> bool {
        self.tcx.region_maps.is_subregion_of(r_sub, r_sup)
    }

    pub fn is_subscope_of(&self, r_sub: ast::NodeId, r_sup: ast::NodeId)
                          -> bool {
        self.tcx.region_maps.is_subscope_of(r_sub, r_sup)
    }

    pub fn mc(&self) -> mc::MemCategorizationContext<'a, ty::ctxt<'tcx>> {
        mc::MemCategorizationContext::new(self.tcx)
    }

    pub fn cat_expr(&self, expr: &ast::Expr) -> mc::cmt {
        match self.mc().cat_expr(expr) {
            Ok(c) => c,
            Err(()) => {
                self.tcx.sess.span_bug(expr.span, "error in mem categorization");
            }
        }
    }

    pub fn cat_expr_unadjusted(&self, expr: &ast::Expr) -> mc::cmt {
        match self.mc().cat_expr_unadjusted(expr) {
            Ok(c) => c,
            Err(()) => {
                self.tcx.sess.span_bug(expr.span, "error in mem categorization");
            }
        }
    }

    pub fn cat_expr_autoderefd(&self,
                               expr: &ast::Expr,
                               adj: &ty::AutoAdjustment)
                               -> mc::cmt {
        let r = match *adj {
            ty::AutoDerefRef(
                ty::AutoDerefRef {
                    autoderefs: autoderefs, ..}) => {
                self.mc().cat_expr_autoderefd(expr, autoderefs)
            }
            ty::AutoAddEnv(..) => {
                // no autoderefs
                self.mc().cat_expr_unadjusted(expr)
            }
        };

        match r {
            Ok(c) => c,
            Err(()) => {
                self.tcx.sess.span_bug(expr.span,
                                       "error in mem categorization");
            }
        }
    }

    pub fn cat_def(&self,
                   id: ast::NodeId,
                   span: Span,
                   ty: ty::t,
                   def: def::Def)
                   -> mc::cmt {
        match self.mc().cat_def(id, span, ty, def) {
            Ok(c) => c,
            Err(()) => {
                self.tcx.sess.span_bug(span, "error in mem categorization");
            }
        }
    }

    pub fn cat_captured_var(&self,
                            closure_id: ast::NodeId,
                            closure_span: Span,
                            upvar_def: def::Def)
                            -> mc::cmt {
        // Create the cmt for the variable being borrowed, from the
        // caller's perspective
        let var_id = upvar_def.def_id().node;
        let var_ty = ty::node_id_to_type(self.tcx, var_id);
        self.cat_def(closure_id, closure_span, var_ty, upvar_def)
    }

    pub fn cat_discr(&self, cmt: mc::cmt, match_id: ast::NodeId) -> mc::cmt {
        Rc::new(mc::cmt_ {
            cat: mc::cat_discr(cmt.clone(), match_id),
            mutbl: cmt.mutbl.inherit(),
            ..*cmt
        })
    }

    pub fn cat_pattern(&self,
                       cmt: mc::cmt,
                       pat: &ast::Pat,
                       op: |mc::cmt, &ast::Pat|) {
        let r = self.mc().cat_pattern(cmt, pat, |_,x,y| op(x,y));
        assert!(r.is_ok());
    }

    pub fn report(&self, err: BckError) {
        self.span_err(
            err.span,
            self.bckerr_to_string(&err).as_slice());
        self.note_and_explain_bckerr(err);
    }

    pub fn report_use_of_moved_value(&self,
                                     use_span: Span,
                                     use_kind: MovedValueUseKind,
                                     lp: &LoanPath,
                                     move: &move_data::Move,
                                     moved_lp: &LoanPath) {
        let verb = match use_kind {
            MovedInUse => "use",
            MovedInCapture => "capture",
        };

        match move.kind {
            move_data::Declared => {
                self.tcx.sess.span_err(
                    use_span,
                    format!("{} of possibly uninitialized variable: `{}`",
                            verb,
                            self.loan_path_to_string(lp)).as_slice());
            }
            _ => {
                let partially = if lp == moved_lp {""} else {"partially "};
                self.tcx.sess.span_err(
                    use_span,
                    format!("{} of {}moved value: `{}`",
                            verb,
                            partially,
                            self.loan_path_to_string(lp)).as_slice());
            }
        }

        match move.kind {
            move_data::Declared => {}

            move_data::MoveExpr => {
                let (expr_ty, expr_span) = move.ty_and_span(self.tcx);
                let suggestion = move_suggestion(self.tcx, expr_ty,
                        "moved by default (use `copy` to override)");
                self.tcx.sess.span_note(
                    expr_span,
                    format!("`{}` moved here because it has type `{}`, which is {}",
                            self.loan_path_to_string(moved_lp),
                            expr_ty.user_string(self.tcx),
                            suggestion).as_slice());
            }

            move_data::MovePat => {
                let (pat_ty, pat_span) = move.ty_and_span(self.tcx);
                self.tcx.sess.span_note(pat_span,
                    format!("`{}` moved here because it has type `{}`, \
                             which is moved by default (use `ref` to \
                             override)",
                            self.loan_path_to_string(moved_lp),
                            pat_ty.user_string(self.tcx)).as_slice());
            }

            move_data::Captured => {
                let (expr_ty, expr_span) = move.ty_and_span(self.tcx);
                let suggestion = move_suggestion(self.tcx, expr_ty,
                        "moved by default (make a copy and \
                         capture that instead to override)");
                self.tcx.sess.span_note(
                    expr_span,
                    format!("`{}` moved into closure environment here because it \
                            has type `{}`, which is {}",
                            self.loan_path_to_string(moved_lp),
                            expr_ty.user_string(self.tcx),
                            suggestion).as_slice());
            }
        }

        fn move_suggestion(tcx: &ty::ctxt, ty: ty::t, default_msg: &'static str)
                          -> &'static str {
            match ty::get(ty).sty {
                ty::ty_closure(box ty::ClosureTy {
                        store: ty::RegionTraitStore(..),
                        ..
                    }) =>
                    "a non-copyable stack closure (capture it in a new closure, \
                     e.g. `|x| f(x)`, to override)",
                _ if ty::type_moves_by_default(tcx, ty) =>
                    "non-copyable (perhaps you meant to use clone()?)",
                _ => default_msg,
            }
        }
    }

    pub fn report_reassigned_immutable_variable(&self,
                                                span: Span,
                                                lp: &LoanPath,
                                                assign:
                                                &move_data::Assignment) {
        self.tcx.sess.span_err(
            span,
            format!("re-assignment of immutable variable `{}`",
                    self.loan_path_to_string(lp)).as_slice());
        self.tcx.sess.span_note(assign.span, "prior assignment occurs here");
    }

    pub fn span_err(&self, s: Span, m: &str) {
        self.tcx.sess.span_err(s, m);
    }

    pub fn span_note(&self, s: Span, m: &str) {
        self.tcx.sess.span_note(s, m);
    }

    pub fn span_end_note(&self, s: Span, m: &str) {
        self.tcx.sess.span_end_note(s, m);
    }

    pub fn bckerr_to_string(&self, err: &BckError) -> String {
        match err.code {
            err_mutbl => {
                let descr = match opt_loan_path(&err.cmt, self.tcx) {
                    None => {
                        format!("{} {}",
                                err.cmt.mutbl.to_user_str(),
                                self.cmt_to_string(&*err.cmt))
                    }
                    Some(lp) => {
                        format!("{} {} `{}`",
                                err.cmt.mutbl.to_user_str(),
                                self.cmt_to_string(&*err.cmt),
                                self.loan_path_to_string(&*lp))
                    }
                };

                match err.cause {
                    euv::ClosureCapture(_) => {
                        format!("closure cannot assign to {}", descr)
                    }
                    euv::OverloadedOperator |
                    euv::AddrOf |
                    euv::RefBinding |
                    euv::AutoRef |
                    euv::ForLoop => {
                        format!("cannot borrow {} as mutable", descr)
                    }
                    euv::ClosureInvocation => {
                        self.tcx.sess.span_bug(err.span,
                            "err_mutbl with a closure invocation");
                    }
                }
            }
            err_out_of_scope(..) => {
                let msg = match opt_loan_path(&err.cmt, self.tcx) {
                    None => "borrowed value".to_string(),
                    Some(lp) => {
                        format!("`{}`", self.loan_path_to_string(&*lp))
                    }
                };
                format!("{} does not live long enough", msg)
            }
            err_borrowed_pointer_too_short(..) => {
                let descr = match opt_loan_path(&err.cmt, self.tcx) {
                    Some(lp) => {
                        format!("`{}`", self.loan_path_to_string(&*lp))
                    }
                    None => self.cmt_to_string(&*err.cmt),
                };

                format!("lifetime of {} is too short to guarantee \
                                its contents can be safely reborrowed",
                               descr)
            }
        }
    }

    pub fn report_aliasability_violation(&self,
                                         span: Span,
                                         kind: AliasableViolationKind,
                                         cause: mc::AliasableReason) {
        let prefix = match kind {
            MutabilityViolation => {
                "cannot assign to data"
            }
            BorrowViolation(euv::ClosureCapture(_)) => {
                // I don't think we can get aliasability violations
                // with closure captures, so no need to come up with a
                // good error message. The reason this cannot happen
                // is because we only capture local variables in
                // closures, and those are never aliasable.
                self.tcx.sess.span_bug(
                    span,
                    "aliasability violation with closure");
            }
            BorrowViolation(euv::OverloadedOperator) |
            BorrowViolation(euv::AddrOf) |
            BorrowViolation(euv::AutoRef) |
            BorrowViolation(euv::RefBinding) => {
                "cannot borrow data mutably"
            }

            BorrowViolation(euv::ClosureInvocation) => {
                "closure invocation"
            }

            BorrowViolation(euv::ForLoop) => {
                "`for` loop"
            }
        };

        match cause {
            mc::AliasableOther => {
                self.tcx.sess.span_err(
                    span,
                    format!("{} in an aliasable location",
                             prefix).as_slice());
            }
            mc::AliasableStatic(..) |
            mc::AliasableStaticMut(..) => {
                self.tcx.sess.span_err(
                    span,
                    format!("{} in a static location", prefix).as_slice());
            }
            mc::AliasableManaged => {
                self.tcx.sess.span_err(
                    span,
                    format!("{} in a `@` pointer", prefix).as_slice());
            }
            mc::AliasableBorrowed => {
                self.tcx.sess.span_err(
                    span,
                    format!("{} in a `&` reference", prefix).as_slice());
            }
        }
    }

    pub fn note_and_explain_bckerr(&self, err: BckError) {
        let code = err.code;
        match code {
            err_mutbl(..) => { }

            err_out_of_scope(super_scope, sub_scope) => {
                note_and_explain_region(
                    self.tcx,
                    "reference must be valid for ",
                    sub_scope,
                    "...");
                let suggestion = if is_statement_scope(self.tcx, super_scope) {
                    "; consider using a `let` binding to increase its lifetime"
                } else {
                    ""
                };
                note_and_explain_region(
                    self.tcx,
                    "...but borrowed value is only valid for ",
                    super_scope,
                    suggestion);
            }

            err_borrowed_pointer_too_short(loan_scope, ptr_scope) => {
                let descr = match opt_loan_path(&err.cmt, self.tcx) {
                    Some(lp) => {
                        format!("`{}`", self.loan_path_to_string(&*lp))
                    }
                    None => self.cmt_to_string(&*err.cmt),
                };
                note_and_explain_region(
                    self.tcx,
                    format!("{} would have to be valid for ",
                            descr).as_slice(),
                    loan_scope,
                    "...");
                note_and_explain_region(
                    self.tcx,
                    format!("...but {} is only valid for ", descr).as_slice(),
                    ptr_scope,
                    "");
            }
        }
    }

    pub fn append_loan_path_to_string(&self,
                                   loan_path: &LoanPath,
                                   out: &mut String) {
        match *loan_path {
            LpUpvar(ty::UpvarId{ var_id: id, closure_expr_id: _ }, _) |
            LpVar(id) => {
                out.push_str(ty::local_var_name_str(self.tcx, id).get());
            }

            LpDowncast(ref lp_base, variant_def_id) => {
                out.push_char('(');
                self.append_loan_path_to_string(&**lp_base, out);
                out.push_str("->");
                out.push_str(ty::item_path_str(self.tcx, variant_def_id).as_slice());
                out.push_char(')');
            }

            LpExtend(ref lp_base, _, LpInterior(mc::InteriorField(fname))) => {
                self.append_autoderefd_loan_path_to_string(&**lp_base, out);
                match fname {
                    mc::NamedField(fname) => {
                        out.push_char('.');
                        out.push_str(token::get_name(fname).get());
                    }
                    mc::PositionalField(idx) => {
                        out.push_char('#'); // invent a notation here
                        out.push_str(idx.to_string().as_slice());
                    }
                }
            }

            LpExtend(ref lp_base, _, LpInterior(mc::InteriorElement(_))) => {
                self.append_autoderefd_loan_path_to_string(&**lp_base, out);
                out.push_str("[..]");
            }

            LpExtend(ref lp_base, _, LpDeref(_)) => {
                out.push_char('*');
                self.append_loan_path_to_string(&**lp_base, out);
            }
        }
    }

    pub fn append_autoderefd_loan_path_to_string(&self,
                                              loan_path: &LoanPath,
                                              out: &mut String) {
        match *loan_path {
            LpDowncast(ref lp_base, variant_def_id) => {
                out.push_char('(');
                self.append_autoderefd_loan_path_to_string(&**lp_base, out);
                out.push_char(':');
                out.push_str(ty::item_path_str(self.tcx, variant_def_id).as_slice());
                out.push_char(')');
            }

            LpExtend(ref lp_base, _, LpDeref(_)) => {
                // For a path like `(*x).f` or `(*x)[3]`, autoderef
                // rules would normally allow users to omit the `*x`.
                // So just serialize such paths to `x.f` or x[3]` respectively.
                self.append_autoderefd_loan_path_to_string(&**lp_base, out)
            }

            LpVar(..) | LpUpvar(..) | LpExtend(_, _, LpInterior(..)) => {
                self.append_loan_path_to_string(loan_path, out)
            }
        }
    }

    pub fn loan_path_to_string(&self, loan_path: &LoanPath) -> String {
        let mut result = String::new();
        self.append_loan_path_to_string(loan_path, &mut result);
        result
    }

    pub fn cmt_to_string(&self, cmt: &mc::cmt_) -> String {
        self.mc().cmt_to_string(cmt)
    }
}

fn is_statement_scope(tcx: &ty::ctxt, region: ty::Region) -> bool {
     match region {
         ty::ReScope(node_id) => {
             match tcx.map.find(node_id) {
                 Some(ast_map::NodeStmt(_)) => true,
                 _ => false
             }
         }
         _ => false
     }
}

impl BitwiseOperator for LoanDataFlowOperator {
    #[inline]
    fn join(&self, succ: uint, pred: uint) -> uint {
        succ | pred // loans from both preds are in scope
    }
}

impl DataFlowOperator for LoanDataFlowOperator {
    #[inline]
    fn initial_value(&self) -> bool {
        false // no loans in scope by default
    }
}

impl Repr for Loan {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("Loan_{:?}({}, {:?}, {:?}-{:?}, {})",
                 self.index,
                 self.loan_path.repr(tcx),
                 self.kind,
                 self.gen_scope,
                 self.kill_scope,
                 self.restricted_paths.repr(tcx))
    }
}

impl Repr for LoanPath {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match self {
            &LpVar(id) => {
                format!("$({})", tcx.map.node_to_string(id))
            }

            &LpUpvar(ty::UpvarId{ var_id, closure_expr_id }, _) => {
                let s = tcx.map.node_to_string(var_id);
                format!("$({} captured by id={})", s, closure_expr_id)
            }

            &LpExtend(ref lp, _, LpDeref(_)) => {
                format!("{}.*", lp.repr(tcx))
            }

            &LpExtend(ref lp, _, LpInterior(ref interior)) => {
                format!("{}.{}", lp.repr(tcx), interior.repr(tcx))
            }

            &LpDowncast(ref lp, variant_def_id) => {
                let variant_str = if variant_def_id.krate == ast::LOCAL_CRATE {
                    ty::item_path_str(tcx, variant_def_id)
                } else {
                    variant_def_id.repr(tcx)
                };
                format!("({}->{})", lp.repr(tcx), variant_str)
            }
        }
    }
}
