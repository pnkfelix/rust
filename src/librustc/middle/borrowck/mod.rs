// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! See doc.rs for a thorough explanation of the borrow checker */

use core;
use core::prelude::*;

use mc = middle::mem_categorization;
use middle::ty;
use middle::typeck;
use middle::moves;
use middle::dataflow::DataFlowContext;
use middle::dataflow::DataFlowOperator;
use util::common::stmt_set;
use util::ppaux::{note_and_explain_region, Repr};

use core::hashmap::{HashSet, HashMap};
use core::io;
use core::result::{Result};
use syntax::ast::{m_mutbl, m_imm, m_const};
use syntax::ast;
use syntax::visit;
use syntax::codemap::span;

macro_rules! if_ok(
    ($inp: expr) => (
        match $inp {
            Ok(v) => { v }
            Err(e) => { return Err(e); }
        }
    )
)

pub mod check_loans;
pub mod gather_loans;

#[path="compute_loans/mod.rs"]
pub mod compute_loans;

pub struct LoanDataFlowOperator;
pub type LoanDataFlow = DataFlowContext<LoanDataFlowOperator>;

pub fn check_crate(
    tcx: ty::ctxt,
    method_map: typeck::method_map,
    moves_map: moves::MovesMap,
    moved_variables_set: moves::MovedVariablesSet,
    capture_map: moves::CaptureMap,
    crate: @ast::crate) -> (root_map, write_guard_map)
{
    let bccx = @BorrowckCtxt {
        tcx: tcx,
        method_map: method_map,
        moves_map: moves_map,
        moved_variables_set: moved_variables_set,
        capture_map: capture_map,
        root_map: root_map(),
        loan_map: @mut HashMap::new(),
        write_guard_map: @mut HashSet::new(),
        stmt_map: @mut HashSet::new(),
        stats: @mut BorrowStats {
            loaned_paths_same: 0,
            loaned_paths_imm: 0,
            stable_paths: 0,
            req_pure_paths: 0,
            guaranteed_paths: 0,
        }
    };

    let v = visit::mk_vt(@visit::Visitor {visit_fn: borrowck_fn,
                                          ..*visit::default_visitor()});
    visit::visit_crate(*crate, bccx, v);

    if tcx.sess.borrowck_stats() {
        io::println(~"--- borrowck stats ---");
        io::println(fmt!("paths requiring guarantees: %u",
                        bccx.stats.guaranteed_paths));
        io::println(fmt!("paths requiring loans     : %s",
                         make_stat(bccx, bccx.stats.loaned_paths_same)));
        io::println(fmt!("paths requiring imm loans : %s",
                         make_stat(bccx, bccx.stats.loaned_paths_imm)));
        io::println(fmt!("stable paths              : %s",
                         make_stat(bccx, bccx.stats.stable_paths)));
        io::println(fmt!("paths requiring purity    : %s",
                         make_stat(bccx, bccx.stats.req_pure_paths)));
    }

    return (bccx.root_map, bccx.write_guard_map);

    fn make_stat(bccx: &BorrowckCtxt, stat: uint) -> ~str {
        let stat_f = stat as float;
        let total = bccx.stats.guaranteed_paths as float;
        fmt!("%u (%.0f%%)", stat  , stat_f * 100f / total)
    }
}

fn borrowck_fn(fk: &visit::fn_kind,
               decl: &ast::fn_decl,
               body: &ast::blk,
               sp: span,
               id: ast::node_id,
               &&self: @BorrowckCtxt,
               v: visit::vt<@BorrowckCtxt>) {
    match fk {
        &visit::fk_anon(*) |
        &visit::fk_fn_block(*) => {
            // Closures are checked as part of their containing fn item.
            visit::visit_fn(fk, decl, body, sp, id, self, v);
        }

        &visit::fk_item_fn(*) |
        &visit::fk_method(*) |
        &visit::fk_dtor(*) => {
            // Check the body of fn items.
            let (id_range, all_loans) =
                gather_loans::gather_loans(self, body);
            let all_loans: &~[Loan] = &*all_loans; // FIXME(#5074)
            let mut dfcx =
                DataFlowContext::new(self.tcx,
                                     self.method_map,
                                     LoanDataFlowOperator,
                                     id_range,
                                     all_loans.len());
            for all_loans.eachi |loan_idx, loan| {
                dfcx.add_gen(loan.gen_scope, loan_idx);
                dfcx.add_kill(loan.kill_scope, loan_idx);
            }
            dfcx.propagate(body);
            check_loans::check_loans(self, &dfcx, *all_loans, body);
        }
    }
}

// ----------------------------------------------------------------------
// Type definitions

pub struct BorrowckCtxt {
    tcx: ty::ctxt,
    method_map: typeck::method_map,
    moves_map: moves::MovesMap,
    moved_variables_set: moves::MovedVariablesSet,
    capture_map: moves::CaptureMap,
    root_map: root_map,
    loan_map: LoanMap,
    write_guard_map: write_guard_map,
    stmt_map: stmt_set,

    // Statistics:
    stats: @mut BorrowStats
}

pub struct BorrowStats {
    loaned_paths_same: uint,
    loaned_paths_imm: uint,
    stable_paths: uint,
    req_pure_paths: uint,
    guaranteed_paths: uint
}

pub struct RootInfo {
    scope: ast::node_id,

    // This will be true if we need to freeze this box at runtime. This will
    // result in a call to `borrow_as_imm()` and `return_to_mut()`.
    freeze: Option<DynaFreezeKind>
}

// a map mapping id's of expressions of gc'd type (@T, @[], etc) where
// the box needs to be kept live to the id of the scope for which they
// must stay live.
pub type root_map = @mut HashMap<root_map_key, RootInfo>;

pub type LoanMap = @mut HashMap<ast::node_id, @Loan>;

// the keys to the root map combine the `id` of the expression with
// the number of types that it is autodereferenced. So, for example,
// if you have an expression `x.f` and x has type ~@T, we could add an
// entry {id:x, derefs:0} to refer to `x` itself, `{id:x, derefs:1}`
// to refer to the deref of the unique pointer, and so on.
#[deriving(Eq, IterBytes)]
pub struct root_map_key {
    id: ast::node_id,
    derefs: uint
}

// A set containing IDs of expressions of gc'd type that need to have a write
// guard.
pub type write_guard_map = @mut HashSet<root_map_key>;

#[deriving(Eq)]
pub enum ReserveReason {
    ReserveForMutField,
    ReserveForBorrowedMut
}

// Errors that can occur
#[deriving(Eq)]
pub enum bckerr_code {
    err_mutbl(ast::mutability),
    err_out_of_root_scope(ty::Region, ty::Region), // superscope, subscope
    err_out_of_scope(ty::Region, ty::Region), // superscope, subscope
    err_partial_freeze_of_managed_content,
    err_cannot_reserve_aliasable_value(ReserveReason),
}

// Combination of an error code and the categorization of the expression
// that caused it
#[deriving(Eq)]
pub struct BckError {
    span: span,
    cmt: mc::cmt,
    code: bckerr_code
}

pub enum MoveError {
    MoveOk,
    MoveFromIllegalCmt(mc::cmt),
    MoveWhileBorrowed(mc::cmt, Loan)
}

pub type BckResult<T> = Result<T, BckError>;

#[deriving(Eq)]
pub enum LoanPath {
    LpVar(ast::node_id),               // `x` in doc.rs
    LpExtend(@LoanPath, mc::MutabilityCategory, LoanPathElem)
}

#[deriving(Eq)]
pub enum LoanPathElem {
    LpDeref,                      // `*LV` in doc.rs
    LpInterior(mc::interior_kind) // `LV.f` in doc.rs
}

#[deriving(Eq)]
pub enum LoanKind {
    MutLoan(ast::mutability, PartialTotal),
    ReserveLoan,
}

pub enum DynaFreezeKind {
    DynaImm,
    DynaMut
}

#[deriving(Eq)]
pub enum PartialTotal {
    Partial,   // Loan affects some portion
    Total      // Loan affects entire path
}

/**
 * Record of a loan that was issued.
 */
pub struct Loan {
    lp: @LoanPath,
    cmt: mc::cmt,
    kind: LoanKind,
    gen_scope: ast::node_id,
    kill_scope: ast::node_id,
    span: span,
}

/// maps computed by `gather_loans` that are then used by `check_loans`
///
/// - `req_loan_map`: map from each block/expr to the required loans needed
///   for the duration of that block/expr
/// - `pure_map`: map from block/expr that must be pure to the error message
///   that should be reported if they are not pure
pub struct ReqMaps {
    req_loan_map: HashMap<ast::node_id, @mut ~[Loan]>,
    pure_map: HashMap<ast::node_id, BckError>
}

pub fn save_and_restore<T:Copy,U>(save_and_restore_t: &mut T,
                                  f: &fn() -> U) -> U {
    let old_save_and_restore_t = *save_and_restore_t;
    let u = f();
    *save_and_restore_t = old_save_and_restore_t;
    u
}

pub fn save_and_restore_managed<T:Copy,U>(save_and_restore_t: @mut T,
                                          f: &fn() -> U) -> U {
    let old_save_and_restore_t = *save_and_restore_t;
    let u = f();
    *save_and_restore_t = old_save_and_restore_t;
    u
}

/// Creates and returns a new root_map

pub fn root_map() -> root_map {
    return @mut HashMap::new();
}

// ___________________________________________________________________________
// Misc

impl ToStr for DynaFreezeKind {
    fn to_str(&self) -> ~str {
        match *self {
            DynaMut => ~"mutable",
            DynaImm => ~"immutable"
        }
    }
}

pub impl BorrowckCtxt {
    fn is_subregion_of(&self, r_sub: ty::Region, r_sup: ty::Region) -> bool {
        self.tcx.region_maps.is_subregion_of(r_sub, r_sup)
    }

    fn cat_expr(&self, expr: @ast::expr) -> mc::cmt {
        mc::cat_expr(self.tcx, self.method_map, expr)
    }

    fn cat_expr_unadjusted(&self, expr: @ast::expr) -> mc::cmt {
        mc::cat_expr_unadjusted(self.tcx, self.method_map, expr)
    }

    fn cat_expr_autoderefd(&self, expr: @ast::expr,
                           adj: @ty::AutoAdjustment) -> mc::cmt {
        match *adj {
            ty::AutoAddEnv(*) => {
                // no autoderefs
                mc::cat_expr_unadjusted(self.tcx, self.method_map, expr)
            }

            ty::AutoDerefRef(
                ty::AutoDerefRef {
                    autoderefs: autoderefs, _}) => {
                mc::cat_expr_autoderefd(self.tcx, self.method_map, expr,
                                        autoderefs)
            }
        }
    }

    fn cat_def(&self,
               id: ast::node_id,
               span: span,
               ty: ty::t,
               def: ast::def) -> mc::cmt {
        mc::cat_def(self.tcx, self.method_map, id, span, ty, def)
    }

    fn cat_discr(&self, cmt: mc::cmt, match_id: ast::node_id) -> mc::cmt {
        @mc::cmt_ {cat:mc::cat_discr(cmt, match_id),
                   ..*cmt}
    }

    fn mc_ctxt(&self) -> mc::mem_categorization_ctxt {
        mc::mem_categorization_ctxt {tcx: self.tcx,
                                 method_map: self.method_map}
    }

    fn cat_pattern(&self,
                   cmt: mc::cmt,
                   pat: @ast::pat,
                   op: &fn(mc::cmt, @ast::pat)) {
        let mc = self.mc_ctxt();
        mc.cat_pattern(cmt, pat, op);
    }

    fn report(&self, err: BckError) {
        self.span_err(
            err.span,
            fmt!("illegal borrow: %s",
                 self.bckerr_to_str(err)));
        self.note_and_explain_bckerr(err);
    }

    fn span_err(&self, s: span, m: ~str) {
        self.tcx.sess.span_err(s, m);
    }

    fn span_note(&self, s: span, m: ~str) {
        self.tcx.sess.span_note(s, m);
    }

    fn bckerr_to_str(&self, err: BckError) -> ~str {
        match err.code {
            err_mutbl(lk) => {
                fmt!("creating %s alias to %s",
                     self.mut_to_str(lk),
                     self.cmt_to_str(err.cmt))
            }
            err_cannot_reserve_aliasable_value(ReserveForBorrowedMut) => {
                ~"cannot reborrow `&mut` pointer in aliasable location"
            }
            err_cannot_reserve_aliasable_value(ReserveForMutField) => {
                ~"cannot borrow mut content in aliasable location"
            }
            err_out_of_root_scope(*) => {
                ~"cannot root managed value long enough"
            }
            err_out_of_scope(*) => {
                ~"borrowed value does not live long enough"
            }
            err_partial_freeze_of_managed_content => {
                ~"cannot partially borrow an `@mut` value"
            }
        }
    }

    fn note_and_explain_bckerr(&self, err: BckError) {
        let code = err.code;
        match code {
            err_cannot_reserve_aliasable_value(_) |
            err_partial_freeze_of_managed_content |
            err_mutbl(*) => {}

            err_out_of_root_scope(super_scope, sub_scope) => {
                note_and_explain_region(
                    self.tcx,
                    ~"managed value would have to be rooted for ",
                    sub_scope,
                    ~"...");
                note_and_explain_region(
                    self.tcx,
                    ~"...but can only be rooted for ",
                    super_scope,
                    ~"");
            }

            err_out_of_scope(super_scope, sub_scope) => {
                note_and_explain_region(
                    self.tcx,
                    ~"borrowed pointer must be valid for ",
                    sub_scope,
                    ~"...");
                note_and_explain_region(
                    self.tcx,
                    ~"...but borrowed value is only valid for ",
                    super_scope,
                    ~"");
          }
        }
    }


    fn cmt_to_str(&self, cmt: mc::cmt) -> ~str {
        let mc = &mc::mem_categorization_ctxt {tcx: self.tcx,
                                               method_map: self.method_map};
        mc.cmt_to_str(cmt)
    }

    fn mut_to_str(&self, mutbl: ast::mutability) -> ~str {
        let mc = &mc::mem_categorization_ctxt {tcx: self.tcx,
                                               method_map: self.method_map};
        mc.mut_to_str(mutbl)
    }
}

impl DataFlowOperator for LoanDataFlowOperator {
    #[inline(always)]
    fn initial_value(&self) -> bool {
        false // no loans in scope by default
    }

    #[inline(always)]
    fn join(&self, succ: uint, pred: uint) -> uint {
        succ | pred // loans from both preds are in scope
    }

    #[inline(always)]
    fn walk_closures(&self) -> bool {
        true
    }
}

impl Repr for Loan {
    fn repr(&self, tcx: ty::ctxt) -> ~str {
        fmt!("Loan(lp=%s, kind=%?, gen_scope=%?, kill_scope=%?)",
             self.lp.repr(tcx),
             self.kind,
             self.gen_scope,
             self.kill_scope)
    }
}

impl Repr for LoanPath {
    fn repr(&self, tcx: ty::ctxt) -> ~str {
        match self {
            &LpVar(id) => {
                fmt!("$(%?)", id)
            }

            &LpExtend(lp, _, LpDeref) => {
                fmt!("%s.*", lp.repr(tcx))
            }

            &LpExtend(lp, _, LpInterior(ref interior)) => {
                fmt!("%s.%s", lp.repr(tcx), interior.repr(tcx))
            }
        }
    }
}
