// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ----------------------------------------------------------------------
// Checking loans
//
// Phase 2 of check: we walk down the tree and check that:
// 1. assignments are always made to mutable locations;
// 2. loans made in overlapping scopes do not conflict
// 3. assignments do not affect things loaned out as immutable
// 4. moves do not affect things loaned out in any way

use core::prelude::*;

use middle::moves;
use middle::borrowck::*;
use mc = middle::mem_categorization;
use middle::ty;
use util::ppaux::ty_to_str;

use core::uint;
use std::oldmap::HashMap;
use syntax::ast::{m_const, m_imm, m_mutbl};
use syntax::ast;
use syntax::ast_util;
use syntax::codemap::span;
use syntax::print::pprust;
use syntax::visit;

struct CheckLoanCtxt {
    bccx: @BorrowckCtxt,
    req_maps: ReqMaps,

    issued_loans: ~[Loan],

    reported: HashMap<ast::node_id, ()>,

    declared_purity: @mut ast::purity,
    fn_args: @mut @~[ast::node_id]
}

// if we are enforcing purity, why are we doing so?
#[deriving_eq]
enum purity_cause {
    // enforcing purity because fn was declared pure:
    pc_pure_fn,

    // enforce purity because we need to guarantee the
    // validity of some alias; `BckError` describes the
    // reason we needed to enforce purity.
    pc_cmt(BckError)
}

pub fn check_loans(bccx: @BorrowckCtxt,
                   req_maps: ReqMaps,
                   crate: @ast::crate) {
    let clcx = @mut CheckLoanCtxt {
        bccx: bccx,
        req_maps: req_maps,
        issued_loans: ~[],
        reported: HashMap(),
        declared_purity: @mut ast::impure_fn,
        fn_args: @mut @~[]
    };
    let vt = visit::mk_vt(@visit::Visitor {visit_expr: check_loans_in_expr,
                                           visit_local: check_loans_in_local,
                                           visit_block: check_loans_in_block,
                                           visit_pat: check_loans_in_pat,
                                           visit_fn: check_loans_in_fn,
                                           .. *visit::default_visitor()});
    visit::visit_crate(*crate, clcx, vt);
}

#[deriving_eq]
enum assignment_type {
    at_straight_up,
    at_swap
}

pub impl assignment_type {
    fn checked_by_liveness(&self) -> bool {
        // the liveness pass guarantees that immutable local variables
        // are only assigned once; but it doesn't consider &mut
        match *self {
          at_straight_up => true,
          at_swap => true
        }
    }
    fn ing_form(&self, desc: ~str) -> ~str {
        match *self {
          at_straight_up => ~"assigning to " + desc,
          at_swap => ~"swapping to and from " + desc
        }
    }
}

pub impl CheckLoanCtxt {
    fn tcx(&self) -> ty::ctxt { self.bccx.tcx }

    fn purity(&self, scope_id: ast::node_id) -> Option<purity_cause> {
        let default_purity = match *self.declared_purity {
          // an unsafe declaration overrides all
          ast::unsafe_fn => return None,

          // otherwise, remember what was declared as the
          // default, but we must scan for requirements
          // imposed by the borrow check
          ast::pure_fn => Some(pc_pure_fn),
          ast::extern_fn | ast::impure_fn => None
        };

        // scan to see if this scope or any enclosing scope requires
        // purity.  if so, that overrides the declaration.

        let mut scope_id = scope_id;
        let region_map = self.tcx().region_map;
        let pure_map = self.req_maps.pure_map;
        loop {
            match pure_map.find(&scope_id) {
              None => (),
              Some(e) => return Some(pc_cmt(e))
            }

            match region_map.find(&scope_id) {
              None => return default_purity,
              Some(next_scope_id) => scope_id = next_scope_id
            }
        }
    }

    // when we are in a pure context, we check each call to ensure
    // that the function which is invoked is itself pure.
    //
    // note: we take opt_expr and expr_id separately because for
    // overloaded operators the callee has an id but no expr.
    // annoying.
    fn check_pure_callee_or_arg(&self,
                                pc: purity_cause,
                                opt_expr: Option<@ast::expr>,
                                callee_id: ast::node_id,
                                callee_span: span) {
        let tcx = self.tcx();

        debug!("check_pure_callee_or_arg(pc=%?, expr=%?, \
                callee_id=%d, ty=%s)",
               pc,
               opt_expr.map(|e| pprust::expr_to_str(*e, tcx.sess.intr()) ),
               callee_id,
               ty_to_str(self.tcx(), ty::node_id_to_type(tcx, callee_id)));

        // Purity rules: an expr B is a legal callee or argument to a
        // call within a pure function A if at least one of the
        // following holds:
        //
        // (a) A was declared pure and B is one of its arguments;
        // (b) B is a stack closure;
        // (c) B is a pure fn;
        // (d) B is not a fn.

        match opt_expr {
          Some(expr) => {
            match expr.node {
              ast::expr_path(_) if pc == pc_pure_fn => {
                let def = self.tcx().def_map.get(&expr.id);
                let did = ast_util::def_id_of_def(def);
                let is_fn_arg =
                    did.crate == ast::local_crate &&
                    (*self.fn_args).contains(&(did.node));
                if is_fn_arg { return; } // case (a) above
              }
              ast::expr_fn_block(*) | ast::expr_loop_body(*) |
              ast::expr_do_body(*) => {
                if self.is_stack_closure(expr.id) {
                    // case (b) above
                    return;
                }
              }
              _ => ()
            }
          }
          None => ()
        }

        let callee_ty = ty::node_id_to_type(tcx, callee_id);
        match ty::get(callee_ty).sty {
            ty::ty_bare_fn(ty::BareFnTy {purity: purity, _}) |
            ty::ty_closure(ty::ClosureTy {purity: purity, _}) => {
                match purity {
                    ast::pure_fn => return, // case (c) above
                    ast::impure_fn | ast::unsafe_fn | ast::extern_fn => {
                        self.report_purity_error(
                            pc, callee_span,
                            fmt!("access to %s function",
                                 purity.to_str()));
                    }
                }
            }
            _ => return, // case (d) above
        }
    }

    // True if the expression with the given `id` is a stack closure.
    // The expression must be an expr_fn_block(*)
    fn is_stack_closure(&self, id: ast::node_id) -> bool {
        let fn_ty = ty::node_id_to_type(self.tcx(), id);
        match ty::get(fn_ty).sty {
            ty::ty_closure(ty::ClosureTy {sigil: ast::BorrowedSigil,
                                          _}) => true,
            _ => false
        }
    }

    fn is_allowed_pure_arg(&self, expr: @ast::expr) -> bool {
        return match expr.node {
          ast::expr_path(_) => {
            let def = self.tcx().def_map.get(&expr.id);
            let did = ast_util::def_id_of_def(def);
            did.crate == ast::local_crate &&
                (*self.fn_args).contains(&(did.node))
          }
          ast::expr_fn_block(*) => self.is_stack_closure(expr.id),
          _ => false,
        };
    }

    fn each_in_scope_loan(&self, scope_id: ast::node_id, op: &fn(&Loan) -> bool) {
        /*!
         *
         * Iterates over each loan which has been issued and which is in
         * scope during `scope_id`. (Note that sometimes loans are issued
         * for scopes that are not yet entered, and hence while they have
         * been issued they may not yet be in scope)
         */

        let region_map = self.tcx().region_map;
        for self.issued_loans.each |loan| {
            if region::scope_contains(region_map, loan.scope, scope_id) {
                if !op(loan) {
                    return;
                }
            }
        }
    }

    fn trigger_loans(&mut self, scope_id: ast::node_id) {
        /*!
         *
         * Trigger loans adds and removes loans that are tried
         * the scope `scope_id`. This method is called on
         * exit from the scope `scope_id`. If `scope_id` is
         * an expression id (typically but not always the case),
         * then `trigger_loans()` will add any loans that the
         * expression creates to `issued_loans`. `trigger_loans()`
         * will also remove any loans with the scope `scope_id`.
         *
         * If `scope_id` represents an expression, the idea is that,
         * during its execution, various loans have been created.
         * Therefore, upon exit from the expression, we can bring
         * those loans into scope and they will endure until their
         * scope expires.  (In fact, in some cases the loans are issued
         * for future scopes that have not yet come to pass)
         */

        let new_loans = match self.req_maps.req_loan_map.find(&scope_id) {
            None => return,
            Some(loans) => loans
        };

        debug!("trigger_loans(%?): %u new loans",
               scope_id,
               new_loans.len());

        // Introduce any new loans that are created during the
        // expression with id `scope_id` (if any)
        for self.each_in_scope_loan(scope_id) |in_scope_loan| {
            for new_loans.each |new_loan| {
                 self.report_error_if_loans_conflict(in_scope_loan, new_loan);
            }
        }
        for new_loans.eachi |i, loan_i| {
            debug!("trigger_loans(%?): new loan %s",
                   scope_id,
                   self.bccx.loan_to_repr(loan_i));
            for new_loans.slice(i+1, new_loans.len()).each |loan_j| {
                self.report_error_if_loans_conflict(loan_i, loan_j);
            }
        }
        let borrowed_new_loans: &~[Loan] = new_loans;
        self.issued_loans.push_all(*borrowed_new_loans);

        // Remove any loans that expire once we exit `scope_id`.
        //
        // NB: This must happen *after* the new loan checking above,
        // since these loans are still considered in scope when the
        // new loans are created.
        if self.issued_loans.any(|l| l.scope == scope_id) {
            self.issued_loans =
                self.issued_loans.filtered(|l| l.scope != scope_id);
        }

        debug!("trigger_loans(%?): %u in scope loans at end",
               scope_id,
               self.issued_loans.len());
    }

    fn report_error_if_loans_conflict(&self,
                                      old_loan: &Loan,
                                      new_loan: &Loan) {
        if old_loan.lp != new_loan.lp {
            return; // The loans refer to different data.
        }

        if old_loan.pt == Partial && new_loan.pt == Partial {
            return; // Only Full loans can conflict with other loans.
        }

        let region_map = self.tcx().region_map;
        if !region::scopes_intersect(region_map,
                                     old_loan.scope,
                                     new_loan.scope) {
            return; // The loans are not in scope at the same time.
        }

        match (old_loan.kind, new_loan.kind) {
            (MutLoan(m_const), MutLoan(_)) |
            (MutLoan(_), MutLoan(m_const)) => {
                // const is compatible with other loans
            }
            (MutLoan(m_imm), MutLoan(m_imm)) => {
                // you can create any number of imm pointers
            }
            (ReserveLoan, ReserveLoan) => {
                // reserve says: do not loan this out, it's
                // ok to reserve more than once
            }

            (ReserveLoan, MutLoan(_)) | (MutLoan(_), ReserveLoan) => {
                self.bccx.span_err(
                    new_loan.cmt.span,
                    fmt!("cannot alias %s \
                          due to prior loan",
                         self.bccx.cmt_to_str(new_loan.cmt)));
                self.bccx.span_note(
                    old_loan.cmt.span,
                    fmt!("prior loan granted here"));
            }

            (MutLoan(om @ m_mutbl), MutLoan(nm)) |
            (MutLoan(om), MutLoan(nm @ m_mutbl)) => {
                self.bccx.span_err(
                    new_loan.cmt.span,
                    fmt!("loan of %s as %s \
                          conflicts with prior loan",
                         self.bccx.cmt_to_str(new_loan.cmt),
                         self.bccx.mut_to_str(nm)));
                self.bccx.span_note(
                    old_loan.cmt.span,
                    fmt!("prior loan as %s granted here",
                         self.bccx.mut_to_str(om)));
            }
        }
    }

    fn is_local_variable(&self, cmt: mc::cmt) -> bool {
        match cmt.cat {
          mc::cat_local(_) => true,
          _ => false
        }
    }

    fn check_assignment(&self, at: assignment_type, ex: @ast::expr) {
        // We don't use cat_expr() here because we don't want to treat
        // auto-ref'd parameters in overloaded operators as rvalues.
        let cmt = match self.bccx.tcx.adjustments.find(&ex.id) {
            None => self.bccx.cat_expr_unadjusted(ex),
            Some(adj) => self.bccx.cat_expr_autoderefd(ex, adj)
        };

        debug!("check_assignment(cmt=%s)",
               self.bccx.cmt_to_repr(cmt));

        if self.is_local_variable(cmt) && at.checked_by_liveness() {
            // liveness guarantees that immutable local variables
            // are only assigned once
        } else {
            match cmt.mutbl {
                mc::McDeclared | mc::McInherited => { /*ok*/ }
                mc::McReadOnly | mc::McImmutable => {
                    self.bccx.span_err(
                        ex.span,
                        at.ing_form(self.bccx.cmt_to_str(cmt)));
                    return;
                }
            }
        }

        // if this is a pure function, only loan-able state can be
        // assigned, because it is uniquely tied to this function and
        // is not visible from the outside
        match self.purity(ex.id) {
          None => (),
          Some(pc_cmt(_)) => {
            // Subtle: Issue #3162.  If we are enforcing purity
            // because there is a reference to aliasable, mutable data
            // that we require to be immutable, we can't allow writes
            // even to data owned by the current stack frame.  This is
            // because that aliasable data might have been located on
            // the current stack frame, we don't know.
            self.report_purity_error(
                self.purity(ex.id).get(),
                ex.span,
                at.ing_form(self.bccx.cmt_to_str(cmt)));
          }
          Some(pc_pure_fn) => {
            if !self.is_owned_by_current_activation(cmt) {
                self.report_purity_error(
                    pc_pure_fn, ex.span,
                    at.ing_form(self.bccx.cmt_to_str(cmt)));
            }
          }
        }

        // check for a conflicting loan as well, except in the case of
        // taking a mutable ref.  that will create a loan of its own
        // which will be checked for compat separately in
        // trigger_loans()
        for self.loan_path(cmt).each |lp| {
            self.check_for_loan_conflicting_with_assignment(
                at, ex, cmt, *lp);
        }

        // Check for and insert write guards as necessary.
        self.add_write_guards_if_necessary(cmt);
    }

    fn is_owned_by_current_activation(&self, cmt: mc::cmt) -> bool {
        match cmt.cat {
            mc::cat_rvalue |
            mc::cat_local(_) |
            mc::cat_arg(_, ast::by_copy) => {
                true
            }
            mc::cat_static_item |
            mc::cat_copied_upvar(_) |
            mc::cat_implicit_self |
            mc::cat_arg(_, ast::by_ref) |
            mc::cat_arg(_, ast::by_val) => {
                false
            }
            mc::cat_deref(cmt_base, _, mc::uniq_ptr(_)) => {
                self.is_owned_by_current_activation(cmt_base)
            }
            mc::cat_deref(_, _, mc::gc_ptr(*)) |
            mc::cat_deref(_, _, mc::region_ptr(*)) |
            mc::cat_deref(_, _, mc::unsafe_ptr(*)) => {
                false
            }
            mc::cat_stack_upvar(cmt_base) |
            mc::cat_interior(cmt_base, _) |
            mc::cat_discr(cmt_base, _) => {
                self.is_owned_by_current_activation(cmt_base)
            }
            mc::cat_self(_) => true,
        }
    }

    fn loan_path(&self, cmt: mc::cmt) -> Option<@LoanPath> {
        /*!
         *
         * Constructs the loan path which would be used for any loans
         * corresponding to `cmt`.  Some categorizations could never
         * be lent, such as an rvalue, so this may return None.
         */

        match cmt.cat {
            mc::cat_rvalue => None,
            mc::cat_static_item => None,
            mc::cat_copied_upvar(id) => Some(@LpVar(id)),
            mc::cat_implicit_self => None,
            mc::cat_local(id) => Some(@LpVar(id)),
            mc::cat_arg(id, ast::by_copy) => Some(@LpVar(id)),
            mc::cat_arg(_, _) => None,
            mc::cat_stack_upvar(cmt) => self.loan_path(cmt),
            mc::cat_deref(cmt_base, _, _) => {
                self.loan_path(cmt_base).map(
                    |p| @LpExtend(*p, cmt.mutbl, LpDeref))
            }
            mc::cat_interior(cmt_base, f) => {
                self.loan_path(cmt_base).map(
                    |p| @LpExtend(*p, cmt.mutbl, LpInterior(f)))
            }
            mc::cat_discr(cmt_base, _) => self.loan_path(cmt_base),
            mc::cat_self(id) => Some(@LpVar(id))
        }
    }

    fn add_write_guards_if_necessary(&self, cmt: mc::cmt) {
        match cmt.cat {
            mc::cat_deref(base, deref_count, ptr_kind) => {
                match ptr_kind {
                    mc::gc_ptr(ast::m_mutbl) => {
                        let key = root_map_key {
                            id: base.id,
                            derefs: deref_count
                        };
                        self.bccx.write_guard_map.insert(key, ());
                    }
                    _ => {}
                }
            }
            mc::cat_interior(base, _) => {
                self.add_write_guards_if_necessary(base);
            }
            _ => {}
        }
    }

    fn check_for_loan_conflicting_with_assignment(&self,
                                                  at: assignment_type,
                                                  ex: @ast::expr,
                                                  cmt: mc::cmt,
                                                  lp: @LoanPath) {
        for self.each_in_scope_loan(ex.id) |loan| {
            if loan.lp == lp {
                match loan.kind {
                    MutLoan(m_const) => {
                        /* ok */
                    }
                    MutLoan(m_mutbl) |
                    MutLoan(m_imm) |
                    ReserveLoan => {
                        self.bccx.span_err(
                            ex.span,
                            fmt!("%s prohibited due to outstanding loan",
                                 at.ing_form(self.bccx.cmt_to_str(cmt))));
                        self.bccx.span_note(
                            loan.cmt.span,
                            fmt!("loan of %s granted here",
                                 self.bccx.cmt_to_str(loan.cmt)));
                        return;
                    }
                }
            }
        }

        // Subtle: if the mutability of the component being assigned
        // is inherited from the thing that the component is embedded
        // within, then we have to check whether that thing has been
        // loaned out as immutable!  An example:
        //    let mut x = {f: Some(3)};
        //    let y = &x; // x loaned out as immutable
        //    x.f = none; // changes type of y.f, which appears to be imm
        match *lp {
            LpExtend(lp_base, mc::McInherited, _) => {
                self.check_for_loan_conflicting_with_assignment(
                    at, ex, cmt, lp_base);
            }

            LpExtend(_, mc::McDeclared, _) => {}
            LpExtend(_, mc::McImmutable, _) => {}
            LpExtend(_, mc::McReadOnly, _) => {}
            LpVar(_) => {}
        }
    }

    fn report_purity_error(&self, pc: purity_cause, sp: span, msg: ~str) {
        match pc {
          pc_pure_fn => {
            self.tcx().sess.span_err(
                sp,
                fmt!("%s prohibited in pure context", msg));
          }
          pc_cmt(ref e) => {
            let reported = self.reported;
            if reported.insert((*e).cmt.id, ()) {
                self.tcx().sess.span_err(
                    (*e).cmt.span,
                    fmt!("illegal borrow unless pure: %s",
                         self.bccx.bckerr_to_str((*e))));
                self.bccx.note_and_explain_bckerr((*e));
                self.tcx().sess.span_note(
                    sp,
                    fmt!("impure due to %s", msg));
            }
          }
        }
    }

    fn check_move_out_from_expr(&self, ex: @ast::expr) {
        match ex.node {
            ast::expr_paren(*) => {
                /* In the case of an expr_paren(), the expression inside
                 * the parens will also be marked as being moved.  Ignore
                 * the parents then so as not to report duplicate errors. */
            }
            _ => {
                let cmt = self.bccx.cat_expr(ex);
                match self.analyze_move_out_from_cmt(cmt) {
                    MoveOk => {}
                    MoveFromIllegalCmt(_) => {
                        self.bccx.span_err(
                            cmt.span,
                            fmt!("moving out of %s",
                                 self.bccx.cmt_to_str(cmt)));
                    }
                    MoveWhileBorrowed(_, loan_cmt) => {
                        self.bccx.span_err(
                            cmt.span,
                            fmt!("moving out of %s prohibited \
                                  due to outstanding loan",
                                 self.bccx.cmt_to_str(cmt)));
                        self.bccx.span_note(
                            loan_cmt.span,
                            fmt!("loan of %s granted here",
                                 self.bccx.cmt_to_str(loan_cmt)));
                    }
                }
            }
        }
    }

    fn analyze_move_out_from_cmt(&self, cmt: mc::cmt) -> MoveError {
        debug!("check_move_out_from_cmt(cmt=%s)",
               self.bccx.cmt_to_repr(cmt));

        match cmt.cat {
            // Rvalues, locals, and arguments can be moved:
            mc::cat_rvalue | mc::cat_local(_) |
            mc::cat_arg(_, ast::by_copy) | mc::cat_self(_) => {}

            // It seems strange to allow a move out of a static item,
            // but what happens in practice is that you have a
            // reference to a constant with a type that should be
            // moved, like `None::<~int>`.  The type of this constant
            // is technically `Option<~int>`, which moves, but we know
            // that the content of static items will never actually
            // contain allocated pointers, so we can just memcpy it.
            mc::cat_static_item => {}

            mc::cat_deref(_, _, mc::unsafe_ptr(*)) => {}

            // Nothing else.
            _ => {
                return MoveFromIllegalCmt(cmt);
            }
        }

        // check for a conflicting loan:
        for self.loan_path(cmt).each |lp| {
            for self.each_in_scope_loan(cmt.id) |loan| {
                if *lp == loan.lp {
                    return MoveWhileBorrowed(cmt, loan.cmt);
                }
            }
        }

        return MoveOk;
    }

    fn check_call(&mut self,
                  expr: @ast::expr,
                  callee: Option<@ast::expr>,
                  callee_id: ast::node_id,
                  callee_span: span,
                  args: &[@ast::expr])
    {
        // There will never be new loans attached to the callee_id,
        // but some loans may have the scope callee_id.
        self.trigger_loans(expr.callee_id);

        match self.purity(expr.id) {
          None => {}
          Some(ref pc) => {
            self.check_pure_callee_or_arg(
                (*pc), callee, callee_id, callee_span);
            for args.each |arg| {
                self.check_pure_callee_or_arg(
                    (*pc), Some(*arg), arg.id, arg.span);
            }
          }
        }
    }
}

fn check_loans_in_fn(fk: &visit::fn_kind,
                     decl: &ast::fn_decl,
                     body: &ast::blk,
                     sp: span,
                     id: ast::node_id,
                     &&self: @mut CheckLoanCtxt,
                     visitor: visit::vt<@mut CheckLoanCtxt>) {
    let is_stack_closure = self.is_stack_closure(id);
    let fty = ty::node_id_to_type(self.tcx(), id);

    let declared_purity;
    match *fk {
        visit::fk_item_fn(*) | visit::fk_method(*) |
        visit::fk_dtor(*) => {
            declared_purity = ty::ty_fn_purity(fty);
        }

        visit::fk_anon(*) | visit::fk_fn_block(*) => {
            let fty_sigil = ty::ty_closure_sigil(fty);
            check_moves_from_captured_variables(self, id, fty_sigil);
            declared_purity = ty::determine_inherited_purity(
                *self.declared_purity,
                ty::ty_fn_purity(fty),
                fty_sigil);
        }
    }

    debug!("purity on entry=%?", copy self.declared_purity);
    do save_and_restore_managed(self.declared_purity) {
        do save_and_restore_managed(self.fn_args) {
            *self.declared_purity = declared_purity;

            match *fk {
                visit::fk_anon(*) |
                visit::fk_fn_block(*) if is_stack_closure => {
                    // inherits the fn_args from enclosing ctxt
                }
                visit::fk_anon(*) | visit::fk_fn_block(*) |
                visit::fk_method(*) | visit::fk_item_fn(*) |
                visit::fk_dtor(*) => {
                    let mut fn_args = ~[];
                    for decl.inputs.each |input| {
                        // For the purposes of purity, only consider function-
                        // typed bindings in trivial patterns to be function
                        // arguments. For example, do not allow `f` and `g` in
                        // (f, g): (&fn(), &fn()) to be called.
                        match input.pat.node {
                            ast::pat_ident(_, _, None) => {
                                fn_args.push(input.pat.id);
                            }
                            _ => {} // Ignore this argument.
                        }
                    }
                    *self.fn_args = @fn_args;
                }
            }

            visit::visit_fn(fk, decl, body, sp, id, self, visitor);
        }
    }
    debug!("purity on exit=%?", copy self.declared_purity);

    fn check_moves_from_captured_variables(self: @mut CheckLoanCtxt,
                                           id: ast::node_id,
                                           fty_sigil: ast::Sigil) {
        match fty_sigil {
            ast::ManagedSigil | ast::OwnedSigil => {
                let cap_vars = self.bccx.capture_map.get(&id);
                for cap_vars.each |cap_var| {
                    match cap_var.mode {
                        moves::CapRef | moves::CapCopy => { loop; }
                        moves::CapMove => { }
                    }
                    let def_id = ast_util::def_id_of_def(cap_var.def).node;
                    let ty = ty::node_id_to_type(self.tcx(), def_id);
                    let cmt = self.bccx.cat_def(id, cap_var.span,
                                                ty, cap_var.def);
                    let move_err = self.analyze_move_out_from_cmt(cmt);
                    match move_err {
                        MoveOk => {}
                        MoveFromIllegalCmt(move_cmt) => {
                            self.bccx.span_err(
                                cap_var.span,
                                fmt!("illegal by-move capture of %s",
                                     self.bccx.cmt_to_str(move_cmt)));
                        }
                        MoveWhileBorrowed(move_cmt, loan_cmt) => {
                            self.bccx.span_err(
                                cap_var.span,
                                fmt!("by-move capture of %s prohibited \
                                      due to outstanding loan",
                                     self.bccx.cmt_to_str(move_cmt)));
                            self.bccx.span_note(
                                loan_cmt.span,
                                fmt!("loan of %s granted here",
                                     self.bccx.cmt_to_str(loan_cmt)));
                        }
                    }
                }
            }

            ast::BorrowedSigil => {}
        }
    }
}

fn check_loans_in_local(local: @ast::local,
                        &&self: @mut CheckLoanCtxt,
                        vt: visit::vt<@mut CheckLoanCtxt>) {
    visit::visit_local(local, self, vt);
}

fn check_loans_in_expr(expr: @ast::expr,
                       &&self: @mut CheckLoanCtxt,
                       vt: visit::vt<@mut CheckLoanCtxt>) {
    debug!("check_loans_in_expr(expr=%?/%s)",
           expr.id, pprust::expr_to_str(expr, self.tcx().sess.intr()));

    visit::visit_expr(expr, self, vt);

    if self.bccx.moves_map.contains_key(&expr.id) {
        self.check_move_out_from_expr(expr);
    }

    match expr.node {
      ast::expr_swap(l, r) => {
        self.check_assignment(at_swap, l);
        self.check_assignment(at_swap, r);
      }
      ast::expr_assign(dest, _) |
      ast::expr_assign_op(_, dest, _) => {
        self.check_assignment(at_straight_up, dest);
      }
      ast::expr_call(f, ref args, _) => {
        self.check_call(expr, Some(f), f.id, f.span, *args);
      }
      ast::expr_method_call(_, _, _, ref args, _) => {
        self.check_call(expr, None, expr.callee_id, expr.span, *args);
      }
      ast::expr_index(_, rval) |
      ast::expr_binary(_, _, rval)
      if self.bccx.method_map.contains_key(&expr.id) => {
        self.check_call(expr,
                        None,
                        expr.callee_id,
                        expr.span,
                        ~[rval]);
      }
      ast::expr_unary(*) | ast::expr_index(*)
      if self.bccx.method_map.contains_key(&expr.id) => {
        self.check_call(expr,
                        None,
                        expr.callee_id,
                        expr.span,
                        ~[]);
      }
      _ => { }
    }

    self.trigger_loans(expr.id);
}

fn check_loans_in_pat(pat: @ast::pat,
                      &&self: @mut CheckLoanCtxt,
                      vt: visit::vt<@mut CheckLoanCtxt>)
{
    self.trigger_loans(pat.id);

    // Note: moves out of pattern bindings are not checked by
    // the borrow checker, at least not directly.  What happens
    // is that if there are any moved bindings, the discriminant
    // will be considered a move, and this will be checked as
    // normal.  Then, in `middle::check_match`, we will check
    // that no move occurs in a binding that is underneath an
    // `@` or `&`.  Together these give the same guarantees as
    // `check_move_out_from_expr()` without requiring us to
    // rewalk the patterns and rebuild the pattern
    // categorizations.
}

fn check_loans_in_block(blk: &ast::blk,
                        &&self: @mut CheckLoanCtxt,
                        vt: visit::vt<@mut CheckLoanCtxt>)
{
    let old_purity = self.declared_purity;

    match blk.node.rules {
        ast::default_blk => {
        }
        ast::unsafe_blk => {
            *self.declared_purity = ast::unsafe_fn;
        }
    }

    visit::visit_block(blk, self, vt);

    self.trigger_loans(blk.node.id);
    self.declared_purity = old_purity;
}

