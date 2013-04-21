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
use util::ppaux::Repr;
use core::hashmap::HashSet;
use syntax::ast;
use syntax::ast_util;
use syntax::visit;
use syntax::codemap::span;

struct CheckLoanCtxt<'self> {
    bccx: @BorrowckCtxt,
    dfcx: &'self LoanDataFlow,
    all_loans: &'self [Loan],
    reported: @mut HashSet<ast::node_id>,
}

pub fn check_loans(bccx: @BorrowckCtxt,
                   dfcx: &LoanDataFlow,
                   all_loans: &[Loan],
                   body: &ast::blk) {
    let clcx = @mut CheckLoanCtxt {
        bccx: bccx,
        dfcx: dfcx,
        all_loans: all_loans,
        reported: @mut HashSet::new(),
    };

    let vt = visit::mk_vt(@visit::Visitor {visit_expr: check_loans_in_expr,
                                           visit_local: check_loans_in_local,
                                           visit_block: check_loans_in_block,
                                           visit_pat: check_loans_in_pat,
                                           visit_fn: check_loans_in_fn,
                                           .. *visit::default_visitor()});
    (vt.visit_block)(body, clcx, vt);
}

#[deriving(Eq)]
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
    fn ing_form(&self, desc: &str) -> ~str {
        match *self {
          at_straight_up => fmt!("assigning to %s", desc),
          at_swap => fmt!("swapping to and from %s", desc)
        }
    }
}

pub impl<'self> CheckLoanCtxt<'self> {
    fn tcx(&self) -> ty::ctxt { self.bccx.tcx }

    fn each_issued_loan(&self,
                        scope_id: ast::node_id,
                        op: &fn(&Loan) -> bool)
    {
        //! Iterates over each loan that that has been issued
        //! on entrance to `scope_id`, regardless of whether it is
        //! actually *in scope* at that point.  Sometimes loans
        //! are issued for future scopes and thus they may have been
        //! *issued* but not yet be in effect.

        for self.dfcx.each_bit_on_entry(scope_id) |loan_index| {
            let loan = &self.all_loans[loan_index];
            if !op(loan) {
                return;
            }
        }
    }

    fn each_in_scope_loan(&self,
                          scope_id: ast::node_id,
                          op: &fn(&Loan) -> bool)
    {
        //! Like `each_issued_loan()`, but only considers loans that are
        //! currently in scope.

        let region_maps = self.tcx().region_maps;
        for self.each_issued_loan(scope_id) |loan| {
            if region_maps.is_sub_scope(scope_id, loan.kill_scope) {
                if !op(loan) {
                    return;
                }
            }
        }
    }

    fn each_loan_issued_by(&self,
                           scope_id: ast::node_id,
                           op: &fn(&Loan) -> bool)
    {
        //! Iterates over each loan originated by `scope_id`.
        //! That is, each loan that is due to `scope_id`.

        for self.dfcx.each_gen_bit(scope_id) |loan_index| {
            let loan = &self.all_loans[loan_index];
            if !op(loan) {
                return;
            }
        }
    }

    fn check_for_conflicting_loans(&mut self, scope_id: ast::node_id) {
        //! Checks to see whether any of the loans that are issued
        //! by `scope_id` conflict with loans that have already been
        //! issued when we enter `scope_id` (for example, we do not
        //! permit two `&mut` borrows of the same variable).

        debug!("check_for_conflicting_loans(scope_id=%?)", scope_id);
        for self.each_issued_loan(scope_id) |issued_loan| {
            for self.each_loan_issued_by(scope_id) |new_loan| {
                 self.report_error_if_loans_conflict(issued_loan, new_loan);
            }
        }
    }

    fn report_error_if_loans_conflict(&self,
                                      old_loan: &Loan,
                                      new_loan: &Loan) {
        debug!("report_error_if_loans_conflict(old_loan=%s, new_loan=%s)",
               old_loan.repr(self.tcx()),
               new_loan.repr(self.tcx()));

        if old_loan.lp != new_loan.lp {
            return; // The loans refer to different data.
        }

        let region_maps = self.tcx().region_maps;
        if !region_maps.scopes_intersect(old_loan.kill_scope,
                                         new_loan.kill_scope) {
            return; // The loans are not in scope at the same time.
        }

        match (old_loan.kind, new_loan.kind) {
            (MutLoan(_, Partial), MutLoan(_, Partial)) => {
                // Partial mut loan just means "some subpath" was
                // borrowed, two such loans don't conflict since the
                // loan path itself was not borrowed.
                return;
            }

            (ReserveLoan, ReserveLoan) => {
                // reserve says: do not loan this out, it's
                // ok to reserve more than once
            }
            (ReserveLoan, MutLoan(_, Partial)) |
            (MutLoan(_, Partial), ReserveLoan) => {
                // The loan path LP is reserved, so no direct aliases
                // to it can be created, but it is ok to alias some
                // subpath of LP.
                return;
            }
            (ReserveLoan, MutLoan(_, Total)) |
            (MutLoan(_, Total), ReserveLoan) => {
                self.bccx.span_err(
                    new_loan.span,
                    fmt!("cannot alias %s \
                          due to prior loan",
                         self.bccx.cmt_to_str(new_loan.cmt)));
                self.bccx.span_note(
                    old_loan.span,
                    fmt!("prior loan granted here"));
            }

            (MutLoan(m_const, _), MutLoan(*)) |
            (MutLoan(*), MutLoan(m_const, _)) => {
                // const is compatible with other loans
            }

            (MutLoan(m_imm, _), MutLoan(m_imm, _)) => {
                // you can create any number of imm pointers
            }

            (MutLoan(om @ m_mutbl, _), MutLoan(nm, _)) |
            (MutLoan(om, _), MutLoan(nm @ m_mutbl, _)) => {
                self.bccx.span_err(
                    new_loan.span,
                    fmt!("loan of %s as %s \
                          conflicts with prior loan",
                         self.bccx.cmt_to_str(new_loan.cmt),
                         self.bccx.mut_to_str(nm)));
                self.bccx.span_note(
                    old_loan.span,
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
            Some(&adj) => self.bccx.cat_expr_autoderefd(ex, adj)
        };

        debug!("check_assignment(cmt=%s)", cmt.repr(self.tcx()));

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

        self.check_for_write_to_aliased_borrowed_mut(at, ex, cmt);

        // check for a conflicting loan as well.
        for self.loan_path(cmt).each |lp| {
            self.check_for_loan_conflicting_with_assignment(
                at, ex, cmt, *lp, Total);
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
            mc::cat_arg(_, ast::by_ref) => {
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
                        self.bccx.write_guard_map.insert(key);
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

    fn check_for_write_to_aliased_borrowed_mut(&self,
                                               at: assignment_type,
                                               ex: @ast::expr,
                                               cmt: mc::cmt) {
        for borrowed_mut_owner(cmt).each |&cmt_owner| {
            if is_aliasable(cmt_owner) {
                self.bccx.span_err(
                    ex.span,
                    fmt!("%s an `&mut` pointer in an aliasable location \
                          prohibited", at.ing_form("")));
            }
        }

        fn borrowed_mut_owner(cmt: mc::cmt) -> Option<mc::cmt> {
            match cmt.cat {
                mc::cat_rvalue => None,
                mc::cat_static_item => None,
                mc::cat_implicit_self => None,
                mc::cat_copied_upvar(*) => None,
                mc::cat_local(*) => None,
                mc::cat_arg(*) => None,
                mc::cat_stack_upvar(b) => borrowed_mut_owner(b),
                mc::cat_deref(_, _, mc::gc_ptr(*)) => None,
                mc::cat_deref(b, _, mc::region_ptr(m_mutbl, _)) => {
                    Some(b)
                }
                mc::cat_deref(_, _, mc::region_ptr(*)) => None,
                mc::cat_deref(_, _, mc::unsafe_ptr(*)) => None,
                mc::cat_deref(b, _, mc::uniq_ptr(*)) => borrowed_mut_owner(b),
                mc::cat_interior(b, _) => borrowed_mut_owner(b),
                mc::cat_discr(b, _) => borrowed_mut_owner(b),
                mc::cat_self(_) => None
            }
        }

        fn is_aliasable(cmt: mc::cmt) -> bool {
            match cmt.cat {
                mc::cat_rvalue(*) => false,
                mc::cat_static_item(*) => true,
                mc::cat_implicit_self(*) => true,
                mc::cat_copied_upvar(*) => false,
                mc::cat_local(*) => false,
                mc::cat_arg(_, ast::by_copy) => false,
                mc::cat_arg(_, ast::by_ref) => true,
                mc::cat_stack_upvar(b) => is_aliasable(b),
                mc::cat_deref(_, _, mc::gc_ptr(*)) => true,
                mc::cat_deref(_, _, mc::region_ptr(m_mutbl, _)) => false,
                mc::cat_deref(_, _, mc::region_ptr(*)) => true,
                mc::cat_deref(_, _, mc::unsafe_ptr(*)) => true,
                mc::cat_deref(b, _, mc::uniq_ptr(*)) => is_aliasable(b),
                mc::cat_interior(b, _) => is_aliasable(b),
                mc::cat_discr(b, _) => is_aliasable(b),
                mc::cat_self(*) => false
            }
        }
    }

    fn check_for_loan_conflicting_with_assignment(&self,
                                                  at: assignment_type,
                                                  ex: @ast::expr,
                                                  cmt: mc::cmt,
                                                  lp: @LoanPath,
                                                  totality: PartialTotal) {
        for self.each_in_scope_loan(ex.id) |loan| {
            // Loan does not apply to this path
            if loan.lp != lp { loop; }

            // Subtle: If totality == Partial, that indicates that the
            // assignment is not to `lp` directly but rather some
            // owned subpath `lp1` of `lp`.  Because `lp1` is owned,
            // it is only mutable iff `lp` is mutable.  Therefore, we
            // looking for immutable loans of `lp`.  We can however
            // ignore partial loans of `lp`, because those only
            // indicate an alias was created to some subpath `lp2` of
            // `lp` and thus the mutability of `lp` itself is
            // unaffected.  This is hard to explain and makes me think
            // that our "partial/total" distinction isn't quite the
            // right one.
            //
            // Here is an example:
            //
            //    let mut v = ~[1, 2, 3];
            //    let p = &const v[0];
            //    v[1] += 1;
            //
            // This should be ok, but without this rule an error would
            // be reported.  This is because of two factors: (1) the
            // const alias `&const v[0]` issues a partial immutable
            // loan for `v`, since doing something like `v = ~[4, 5,
            // 6]` would free the old vector content and thus
            // invalidate `p`. Then (2) the assignment to `v[1]` is
            // only legal if `v` is mutable, but there is a (partial)
            // *immutable* loan of `v`, so an error is reported.
            if totality == Partial {
                match loan.kind {
                    MutLoan(_, Partial) => { loop; }
                    MutLoan(_, Total) |
                    ReserveLoan => {}
                }
            }

            match loan.kind {
                MutLoan(m_const, _) => {
                    /* ok */
                }
                MutLoan(m_mutbl, _) |
                MutLoan(m_imm, _) |
                ReserveLoan => {
                    self.bccx.span_err(
                        ex.span,
                        fmt!("%s prohibited due to outstanding loan",
                             at.ing_form(self.bccx.cmt_to_str(cmt))));
                    self.bccx.span_note(
                        loan.span,
                        fmt!("loan of %s granted here",
                             self.bccx.cmt_to_str(loan.cmt)));
                    return;
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
        // Also see the "Subtle" note above in this function.
        match *lp {
            LpExtend(lp_base, mc::McInherited, _) => {
                self.check_for_loan_conflicting_with_assignment(
                    at, ex, cmt, lp_base, Partial);
            }

            LpExtend(_, mc::McDeclared, _) => {}
            LpExtend(_, mc::McImmutable, _) => {}
            LpExtend(_, mc::McReadOnly, _) => {}
            LpVar(_) => {}
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
                    MoveWhileBorrowed(_, loan) => {
                        self.bccx.span_err(
                            cmt.span,
                            fmt!("moving out of %s prohibited \
                                  due to outstanding loan",
                                 self.bccx.cmt_to_str(cmt)));
                        self.bccx.span_note(
                            loan.span,
                            fmt!("loan of %s granted here",
                                 self.bccx.cmt_to_str(loan.cmt)));
                    }
                }
            }
        }
    }

    fn analyze_move_out_from_cmt(&self, cmt: mc::cmt) -> MoveError {
        debug!("check_move_out_from_cmt(cmt=%s)", cmt.repr(self.tcx()));

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
                    return MoveWhileBorrowed(cmt, *loan);
                }
            }
        }

        return MoveOk;
    }

    fn check_call(&mut self,
                  _expr: @ast::expr,
                  _callee: Option<@ast::expr>,
                  callee_id: ast::node_id,
                  _callee_span: span,
                  _args: &[@ast::expr])
    {
        // NB: This call to check for conflicting loans is not truly
        // necessary, because the callee_id never issues new loans.
        // However, I added it for consistency and lest the system
        // should change in the future.
        self.check_for_conflicting_loans(callee_id);
    }
}

fn check_loans_in_fn<'a>(fk: &visit::fn_kind,
                         decl: &ast::fn_decl,
                         body: &ast::blk,
                         sp: span,
                         id: ast::node_id,
                         &&self: @mut CheckLoanCtxt<'a>,
                         visitor: visit::vt<@mut CheckLoanCtxt<'a>>) {
    match *fk {
        visit::fk_item_fn(*) |
        visit::fk_method(*) |
        visit::fk_dtor(*) => {
            // Don't process nested items.
            return;
        }

        visit::fk_anon(*) |
        visit::fk_fn_block(*) => {
            let fty = ty::node_id_to_type(self.tcx(), id);
            let fty_sigil = ty::ty_closure_sigil(fty);
            check_moves_from_captured_variables(self, id, fty_sigil);
        }
    }

    visit::visit_fn(fk, decl, body, sp, id, self, visitor);

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
                        MoveWhileBorrowed(move_cmt, loan) => {
                            self.bccx.span_err(
                                cap_var.span,
                                fmt!("by-move capture of %s prohibited \
                                      due to outstanding loan",
                                     self.bccx.cmt_to_str(move_cmt)));
                            self.bccx.span_note(
                                loan.span,
                                fmt!("loan of %s granted here",
                                     self.bccx.cmt_to_str(loan.cmt)));
                        }
                    }
                }
            }

            ast::BorrowedSigil => {}
        }
    }
}

fn check_loans_in_local<'a>(local: @ast::local,
                            &&self: @mut CheckLoanCtxt<'a>,
                            vt: visit::vt<@mut CheckLoanCtxt<'a>>) {
    visit::visit_local(local, self, vt);
}

fn check_loans_in_expr<'a>(expr: @ast::expr,
                           &&self: @mut CheckLoanCtxt<'a>,
                           vt: visit::vt<@mut CheckLoanCtxt<'a>>) {
    debug!("check_loans_in_expr(expr=%s)",
           expr.repr(self.tcx()));

    visit::visit_expr(expr, self, vt);

    self.check_for_conflicting_loans(expr.id);

    if self.bccx.moves_map.contains(&expr.id) {
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
}

fn check_loans_in_pat<'a>(pat: @ast::pat,
                          &&self: @mut CheckLoanCtxt<'a>,
                          vt: visit::vt<@mut CheckLoanCtxt<'a>>)
{
    self.check_for_conflicting_loans(pat.id);

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

    visit::visit_pat(pat, self, vt);
}

fn check_loans_in_block<'a>(blk: &ast::blk,
                            &&self: @mut CheckLoanCtxt<'a>,
                            vt: visit::vt<@mut CheckLoanCtxt<'a>>)
{
    visit::visit_block(blk, self, vt);
    self.check_for_conflicting_loans(blk.node.id);
}

