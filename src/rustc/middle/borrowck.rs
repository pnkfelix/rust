import syntax::ast;
import syntax::ast::{m_mutbl, m_imm, m_const};
import syntax::visit;
import syntax::ast_util;
import syntax::codemap::span;
import util::ppaux::{ty_to_str, region_to_str};
import driver::session::session;
import std::map::{int_hash, hashmap, set};
import std::list;
import std::list::{list, cons, nil};
import result::{result, ok, err, extensions};
import syntax::print::pprust;
import util::common::indenter;

export check_crate, root_map;

fn check_crate(tcx: ty::ctxt,
               method_map: typeck::method_map,
               crate: @ast::crate) -> root_map {
    let bccx = @{tcx: tcx, method_map: method_map,
                 root_map: int_hash(), in_ctor: none};
    let req_loan_map = gather_loans(bccx, crate);
    check_loans(bccx, req_loan_map, crate);
    ret bccx.root_map;
}

// ----------------------------------------------------------------------
// Type definitions

type borrowck_ctxt = @{tcx: ty::ctxt,
                       method_map: typeck::method_map,
                       root_map: root_map,

                       // Keep track of whether we're inside a ctor, so as to
                       // allow mutating immutable fields in the same class if
                       // we are in a ctor, we track the self id
                       in_ctor: option<ast::node_id>};

// a map mapping id's of expressions of task-local type (@T, []/@, etc) where
// the box needs to be kept live to the id of the scope for which they must
// stay live.
type root_map = hashmap<ast::node_id, ast::node_id>;

enum bckerr_code {
    err_mutbl(ast::mutability, ast::mutability),
    err_mut_uniq,
    err_preserve_gc
}

type bckerr = {cmt: cmt, code: bckerr_code};

type bckres<T> = result<T, bckerr>;

enum loan_path {
    lp_local(ast::node_id),
    lp_arg(ast::node_id),
    lp_deref(@loan_path),
    lp_field(@loan_path, str),
    lp_index(@loan_path)
}

enum rvalue_kind {
    rv_method,
    rv_static_item,
    rv_upvar,
    rv_misc,
    rv_self
}

enum categorization {
    cat_rvalue(rvalue_kind),
    cat_deref(cmt),
    cat_field(cmt, str),
    cat_index(cmt),
    cat_local(ast::node_id),
    cat_arg(ast::node_id),
}

type cmt = @{expr: @ast::expr,        // the expr being categorized
             cat: categorization,     // categorization of expr
             lp: option<@loan_path>,  // loan path for expr, if any
             mutbl: ast::mutability,  // mutability of expr as lvalue
             ty: ty::t};              // type of the expr

type loan = {lp: @loan_path, cmt: cmt, mutbl: ast::mutability};

fn sup_mutbl(req_m: ast::mutability,
             act_m: ast::mutability) -> bool {
    alt (req_m, act_m) {
      (m_const, _) |
      (m_imm, m_imm) |
      (m_mutbl, m_mutbl) {
        true
      }

      (_, m_const) |
      (m_imm, m_mutbl) |
      (m_mutbl, m_imm) {
        false
      }
    }
}

fn check_sup_mutbl(req_m: ast::mutability,
                   cmt: cmt) -> bckres<()> {
    if sup_mutbl(req_m, cmt.mutbl) {
        ok(())
    } else {
        err({cmt:cmt, code:err_mutbl(req_m, cmt.mutbl)})
    }
}

// ----------------------------------------------------------------------
// Gathering loans
//
// The borrow check proceeds in two phases. In phase one, we gather the full
// set of loans that are required at any point.  These are sorted according to
// their associated scopes.  In phase two, checking loans, we will then make
// sure that all of these loans are honored.

// Maps a scope to a list of loans that were issued within that scope.
type req_loan_map = hashmap<ast::node_id, @mut [@const [loan]]>;

enum gather_loan_ctxt = @{bccx: borrowck_ctxt, req_loan_map: req_loan_map};

fn gather_loans(bccx: borrowck_ctxt, crate: @ast::crate) -> req_loan_map {
    let glcx = gather_loan_ctxt(@{bccx: bccx, req_loan_map: int_hash()});
    let v = visit::mk_vt(@{visit_expr: req_loans_in_expr
                           with *visit::default_visitor()});
    visit::visit_crate(*crate, glcx, v);
    ret glcx.req_loan_map;
}

fn req_loans_in_expr(ex: @ast::expr,
                     &&self: gather_loan_ctxt,
                     vt: visit::vt<gather_loan_ctxt>) {
    let bccx = self.bccx;
    let tcx = bccx.tcx;

    // If this expression is borrowed, have to ensure it remains valid:
    for tcx.borrowings.find(ex.id).each { |scope_id|
        let cmt = self.bccx.cat_borrow_of_expr(ex);
        self.guarantee_valid(cmt, m_const, ty::re_scope(scope_id));
    }

    // Special checks for various kinds of expressions:
    alt ex.node {
      ast::expr_addr_of(mutbl, base) {
        let base_cmt = self.bccx.cat_expr(base);

        // make sure that if we taking an &mut or &imm ptr, the thing it
        // points at is mutable or immutable respectively:
        self.bccx.report_if_err(
            check_sup_mutbl(mutbl, base_cmt).chain { |_ok|
                // make sure that the thing we are pointing out stays valid
                // for the lifetime `scope_r`:
                let scope_r =
                    alt check ty::get(ty::expr_ty(tcx, ex)).struct {
                      ty::ty_rptr(r, _) { r }
                    };
                self.guarantee_valid(base_cmt, mutbl, scope_r);
                ok(())
            });
      }

      ast::expr_call(f, args, _) {
        let arg_tys = ty::ty_fn_args(ty::expr_ty(self.tcx(), f));
        vec::iter2(args, arg_tys) { |arg, arg_ty|
            alt ty::resolved_mode(self.tcx(), arg_ty.mode) {
              ast::by_mutbl_ref {
                let arg_cmt = self.bccx.cat_expr(arg);
                self.guarantee_valid(arg_cmt, m_mutbl, ty::re_scope(ex.id));
              }
              ast::by_ref {
                let arg_cmt = self.bccx.cat_expr(arg);
                self.guarantee_valid(arg_cmt, m_const, ty::re_scope(ex.id));
              }
              ast::by_move | ast::by_copy | ast::by_val {}
            }
        }
      }
      _ { /*ok*/ }
    }

    // Check any contained expressions:
    visit::visit_expr(ex, self, vt);
}

impl methods for gather_loan_ctxt {
    fn tcx() -> ty::ctxt { self.bccx.tcx }

    // guarantees that addr_of(cmt) will be valid for the duration of
    // `scope_r`, or reports an error.  This may entail taking out loans,
    // which will be added to the `req_loan_map`.
    fn guarantee_valid(cmt: cmt,
                       mutbl: ast::mutability,
                       scope_r: ty::region) {

        #debug["guarantee_valid(expr=%s, cmt=%s, mutbl=%s, scope_r=%s)",
               pprust::expr_to_str(cmt.expr),
               self.bccx.cmt_to_repr(cmt),
               self.bccx.mut_to_str(mutbl),
               region_to_str(self.tcx(), scope_r)];
        let _i = indenter();

        alt cmt.lp {
          // If this expression is a loanable path, we MUST take out a loan.
          // This is somewhat non-obvious.  You might think, for example, that
          // if we have an immutable local variable `x` whose value is being
          // borrowed, we could rely on `x` not to change.  This is not so,
          // however, because even immutable locals can be moved.  So we take
          // out a loan on `x`, guaranteeing that it remains immutable for the
          // duration of the reference: if there is an attempt to move it
          // within that scope, the loan will be detected and an error will be
          // reported.
          some(_) {
            alt scope_r {
              ty::re_scope(scope_id) {
                alt self.bccx.loan(cmt, mutbl) {
                  ok(loans) { self.add_loans(scope_id, loans); }
                  err(e) { self.bccx.report(e); }
                }
              }
              _ {
                self.tcx().sess.span_warn(
                    cmt.expr.span,
                    #fmt["Cannot guarantee the stability \
                          of this expression for the entirety of \
                          its lifetime, %s",
                         region_to_str(self.tcx(), scope_r)]);
              }
            }
          }

          // The path is not loanable: in that case, we must try and preserve
          // it dynamically (or see that it is preserved by virtue of being
          // rooted in some immutable path)
          none {
            self.bccx.report_if_err(
                check_sup_mutbl(mutbl, cmt).chain { |_ok|
                    let opt_scope_id = alt scope_r {
                      ty::re_scope(scope_id) { some(scope_id) }
                      _ { none }
                    };

                    self.bccx.preserve(cmt, opt_scope_id)
                })
          }
        }
    }

    fn add_loans(scope_id: ast::node_id, loans: @const [loan]) {
        alt self.req_loan_map.find(scope_id) {
          some(l) {
            *l += [loans];
          }
          none {
            self.req_loan_map.insert(scope_id, @mut [loans]);
          }
        }
    }
}

// ----------------------------------------------------------------------
// Checking loans
//
// Phase 2 of check: we walk down the tree and check that:
// 1. assignments are always made to mutable locations;
// 2. loans made in overlapping scopes do not conflict
// 3. assignments do not affect things loaned out as immutable
// 4. moves to dnot affect things loaned out in any way

enum check_loan_ctxt = @{
    bccx: borrowck_ctxt,
    req_loan_map: req_loan_map
};

fn check_loans(bccx: borrowck_ctxt,
               req_loan_map: req_loan_map,
               crate: @ast::crate) {
    let clcx = check_loan_ctxt(@{bccx: bccx, req_loan_map: req_loan_map});
    let vt = visit::mk_vt(@{visit_expr: check_loans_in_expr,
                            visit_block: check_loans_in_block
                            with *visit::default_visitor()});
    visit::visit_crate(*crate, clcx, vt);
}

impl methods for check_loan_ctxt {
    fn tcx() -> ty::ctxt { self.bccx.tcx }

    fn walk_loans(scope_id: ast::node_id,
                  f: fn(loan) -> bool) {
        let mut scope_id = scope_id;
        let parents = self.tcx().region_map.parents;
        let req_loan_map = self.req_loan_map;

        loop {
            for req_loan_map.find(scope_id).each { |loanss|
                for (*loanss).each { |loans|
                    for (*loans).each { |loan|
                        if !f(loan) { ret; }
                    }
                }
            }

            alt parents.find(scope_id) {
              none { ret; }
              some(next_scope_id) { scope_id = next_scope_id; }
            }
        }
    }

    fn walk_loans_of(scope_id: ast::node_id,
                     lp: @loan_path,
                     f: fn(loan) -> bool) {
        for self.walk_loans(scope_id) { |loan|
            if loan.lp == lp {
                if !f(loan) { ret; }
            }
        }
    }

    fn check_for_conflicting_loans(scope_id: ast::node_id) {
        let new_loanss = alt self.req_loan_map.find(scope_id) {
            none { ret; }
            some(loanss) { loanss }
        };

        let par_scope_id = self.tcx().region_map.parents.get(scope_id);
        for self.walk_loans(par_scope_id) { |old_loan|
            for (*new_loanss).each { |new_loans|
                for (*new_loans).each { |new_loan|
                    if old_loan.lp != new_loan.lp { cont; }
                    alt (old_loan.mutbl, new_loan.mutbl) {
                      (m_const, _) | (_, m_const) |
                      (m_mutbl, m_mutbl) | (m_imm, m_imm) {
                        /*ok*/
                      }

                      (m_mutbl, m_imm) | (m_imm, m_mutbl) {
                        self.tcx().sess.span_warn(
                            new_loan.cmt.expr.span,
                            #fmt["Loan of %s as %s \
                                  conflicts with prior loan",
                                 self.bccx.cmt_to_str(new_loan.cmt),
                                 self.bccx.mut_to_str(new_loan.mutbl)]);
                        self.tcx().sess.span_note(
                            old_loan.cmt.expr.span,
                            #fmt["Prior loan as %s granted here",
                                 self.bccx.mut_to_str(old_loan.mutbl)]);
                      }
                    }
                }
            }
        }
    }

    fn check_assignment(ex: @ast::expr) {
        let cmt = self.bccx.cat_expr(ex);

        alt cmt.mutbl {
          m_mutbl { /*ok*/ }
          m_const | m_imm {
            self.tcx().sess.span_warn(
                ex.span,
                #fmt["Cannot assign to %s", self.bccx.cmt_to_str(cmt)]);
            ret;
          }
        }

        // check for a conflicting loan as well
        let lp = alt cmt.lp {
          none { ret; }
          some(lp) { lp }
        };
        for self.walk_loans_of(ex.id, lp) { |loan|
            alt loan.mutbl {
              m_mutbl | m_const { /*ok*/ }
              m_imm {
                self.tcx().sess.span_warn(
                    ex.span,
                    #fmt["Cannot assign to %s due to outstanding loan",
                         self.bccx.cmt_to_str(cmt)]);
                self.tcx().sess.span_note(
                    loan.cmt.expr.span,
                    #fmt["Loan of %s granted here",
                         self.bccx.cmt_to_str(loan.cmt)]);
                ret;
              }
            }
        }
    }

    fn check_move_out(ex: @ast::expr) {
        let cmt = self.bccx.cat_expr(ex);

        alt cmt.cat {
          // Rvalues and locals can be moved:
          cat_rvalue(_) | cat_local(_) { /*ok*/ }

          // Owned arguments can be moved:
          cat_arg(_) if cmt.mutbl == m_mutbl { /*ok*/ }

          // Nothing else.
          _ {
            self.tcx().sess.span_warn(
                ex.span,
                #fmt["Cannot move from %s", self.bccx.cmt_to_str(cmt)]);
            ret;
          }
        }

        // check for a conflicting loan:
        let lp = alt cmt.lp {
          none { ret; }
          some(lp) { lp }
        };
        for self.walk_loans_of(ex.id, lp) { |loan|
            self.tcx().sess.span_warn(
                ex.span,
                #fmt["Cannot move from %s due to outstanding loan",
                     self.bccx.cmt_to_str(cmt)]);
            self.tcx().sess.span_note(
                loan.cmt.expr.span,
                #fmt["Loan of %s granted here",
                     self.bccx.cmt_to_str(loan.cmt)]);
            ret;
        }
    }
}

fn check_loans_in_expr(expr: @ast::expr,
                       &&self: check_loan_ctxt,
                       vt: visit::vt<check_loan_ctxt>) {
    self.check_for_conflicting_loans(expr.id);
    alt expr.node {
      ast::expr_swap(l, r) {
        self.check_assignment(l);
        self.check_assignment(r);
      }
      ast::expr_move(dest, src) {
        self.check_assignment(dest);
        self.check_move_out(src);
      }
      ast::expr_assign(dest, _) |
      ast::expr_assign_op(_, dest, _) {
        self.check_assignment(dest);
      }
      ast::expr_call(f, args, _) {
        let arg_tys = ty::ty_fn_args(ty::expr_ty(self.tcx(), f));
        vec::iter2(args, arg_tys) { |arg, arg_ty|
            alt ty::resolved_mode(self.tcx(), arg_ty.mode) {
              ast::by_move {
                self.check_move_out(arg);
              }
              ast::by_mutbl_ref |
              ast::by_ref {
                // these are translated into loans
              }
              ast::by_copy | ast::by_val {
              }
            }
        }
      }
      _ { }
    }
    visit::visit_expr(expr, self, vt);
}

fn check_loans_in_block(blk: ast::blk,
                        &&self: check_loan_ctxt,
                        vt: visit::vt<check_loan_ctxt>) {
    self.check_for_conflicting_loans(blk.node.id);
    visit::visit_block(blk, self, vt)
}

// ----------------------------------------------------------------------
// Categorization
//
// Imagine a routine ToAddr(Expr) that evaluates an expression and returns an
// address where the result is to be found.  If Expr is an lvalue, then this
// is the address of the lvalue.  If Expr is an rvalue, this is the address of
// some temporary spot in memory where the result is stored.
//
// Now, cat_expr() classies the expression Expr and the address A=ToAddr(Expr)
// as follows:
//
// - cat: what kind of expression was this?  This is a subset of the
//   full expression forms which only includes those that we care about
//   for the purpose of the analysis.
// - mutbl: mutability of the address A
// - ty: the type of data found at the address A
//
// The resulting categorization tree differs somewhat from the expressions
// themselves.  For example, auto-derefs are explicit.  Also, an index a[b] is
// decomposed into two operations: a derefence to reach the array data and
// then an index to jump forward to the relevant item.

// Categorizes a derefable type.  Note that we include vectors and strings as
// derefable (we model an index as the combination of a deref and then a
// pointer adjustment).
enum deref_kind { uniqish, gcish, regionish, unsafeish, abstractionish }
fn deref_kind(tcx: ty::ctxt, t: ty::t) -> deref_kind {
    alt ty::get(t).struct {
      ty::ty_uniq(*) | ty::ty_vec(*) | ty::ty_str |
      ty::ty_evec(_, ty::vstore_uniq) |
      ty::ty_estr(ty::vstore_uniq) {
        uniqish
      }

      ty::ty_rptr(*) |
      ty::ty_evec(_, ty::vstore_slice(_)) |
      ty::ty_estr(ty::vstore_slice(_)) {
        regionish
      }

      ty::ty_box(*) |
      ty::ty_evec(_, ty::vstore_box) |
      ty::ty_estr(ty::vstore_box) {
        gcish
      }

      ty::ty_ptr(*) {
        unsafeish
      }

      ty::ty_enum(*) | ty::ty_res(*) {
        abstractionish
      }

      _ {
        tcx.sess.bug(
            #fmt["deref_cat() invoked on non-derefable type %s",
                 ty_to_str(tcx, t)]);
      }
    }
}

impl categorize_methods for borrowck_ctxt {
    fn cat_borrow_of_expr(expr: @ast::expr) -> cmt {
        // a borrowed expression must be either an @, ~, or a vec/@, vec/~
        let expr_ty = ty::expr_ty(self.tcx, expr);
        alt ty::get(expr_ty).struct {
          ty::ty_vec(*) | ty::ty_evec(*) |
          ty::ty_str | ty::ty_estr(*) {
            self.cat_index(expr, expr)
          }

          ty::ty_uniq(*) | ty::ty_box(*) | ty::ty_rptr(*) {
            let cmt = self.cat_expr(expr);
            self.cat_deref(expr, cmt).get()
          }

          _ {
            self.tcx.sess.span_bug(
                expr.span,
                #fmt["Borrowing of non-derefable type `%s`",
                     ty_to_str(self.tcx, expr_ty)]);
          }
        }
    }

    fn cat_expr(expr: @ast::expr) -> cmt {
        let tcx = self.tcx;
        let expr_ty = ty::expr_ty(tcx, expr);

        if self.method_map.contains_key(expr.id) {
            ret @{expr:expr, cat:cat_rvalue(rv_method), lp:none,
                  mutbl:m_imm, ty:expr_ty};
        }

        alt expr.node {
          ast::expr_unary(ast::deref, e_base) {
            let base_cmt = self.cat_expr(e_base);
            alt self.cat_deref(expr, base_cmt) {
              some(cmt) { ret cmt; }
              none {
                tcx.sess.span_bug(
                    e_base.span,
                    #fmt["Explicit deref of non-derefable type `%s`",
                         ty_to_str(tcx, ty::expr_ty(tcx, e_base))]);
              }
            }
          }

          ast::expr_field(base, f_name, _) {
            let base_cmt = self.cat_autoderef(expr, base);
            let f_mutbl = alt field_mutbl(tcx, base_cmt.ty, f_name) {
              some(f_mutbl) { f_mutbl }
              none {
                tcx.sess.span_bug(
                    expr.span,
                    #fmt["Cannot find field `%s` in type `%s`",
                         f_name, ty_to_str(tcx, base_cmt.ty)]);
              }
            };
            let m = alt f_mutbl {
              m_imm { base_cmt.mutbl } // imm: as mutable as the container
              m_mutbl | m_const { f_mutbl }
            };
            let lp = base_cmt.lp.map { |lp| @lp_field(lp, f_name) };
            @{expr: expr, cat: cat_field(base_cmt, f_name), lp:lp,
              mutbl: m, ty: expr_ty}
          }

          ast::expr_index(base, _) {
            self.cat_index(expr, base)
          }

          ast::expr_path(_) {
            let def = self.tcx.def_map.get(expr.id);
            self.cat_def(expr, expr_ty, def)
          }

          ast::expr_addr_of(*) | ast::expr_call(*) | ast::expr_bind(*) |
          ast::expr_swap(*) | ast::expr_move(*) | ast::expr_assign(*) |
          ast::expr_assign_op(*) | ast::expr_fn(*) | ast::expr_fn_block(*) |
          ast::expr_assert(*) | ast::expr_check(*) | ast::expr_ret(*) |
          ast::expr_be(*) | ast::expr_loop_body(*) | ast::expr_unary(*) |
          ast::expr_copy(*) | ast::expr_cast(*) | ast::expr_fail(*) |
          ast::expr_vstore(*) | ast::expr_vec(*) | ast::expr_tup(*) |
          ast::expr_if_check(*) | ast::expr_if(*) | ast::expr_log(*) |
          ast::expr_new(*) | ast::expr_binary(*) | ast::expr_while(*) |
          ast::expr_do_while(*) | ast::expr_block(*) | ast::expr_loop(*) |
          ast::expr_alt(*) | ast::expr_lit(*) | ast::expr_break |
          ast::expr_mac(*) | ast::expr_cont | ast::expr_rec(*) {
            @{expr:expr, cat:cat_rvalue(rv_misc), lp:none,
              mutbl:m_imm, ty:expr_ty}
          }
        }
    }

    fn cat_deref(expr: @ast::expr, base_cmt: cmt) -> option<cmt> {
        ty::deref(self.tcx, base_cmt.ty).map { |mt|
            let lp = base_cmt.lp.chain { |lp|
                alt deref_kind(self.tcx, base_cmt.ty) {
                  uniqish | abstractionish {some(@lp_deref(lp))}
                  unsafeish | gcish | regionish {none}
                }
            };
            @{expr:expr, cat:cat_deref(base_cmt), lp:lp,
              mutbl:mt.mutbl, ty:mt.ty}
        }
    }

    fn cat_autoderef(expr: @ast::expr, base: @ast::expr) -> cmt {
        // Creates a string of implicit derefences so long as base is
        // dereferencable.  n.b., it is important that these dereferences are
        // associated with the field/index that caused the autoderef (expr).
        // This is used later to adjust ref counts and so forth in trans.

        // Given something like base.f where base has type @m1 @m2 T, we want
        // to yield the equivalent categories to (**base).f.
        let mut cmt = self.cat_expr(base);
        loop {
            alt self.cat_deref(expr, cmt) {
              none { ret cmt; }
              some(cmt1) { cmt = cmt1; }
            }
        }
    }

    fn cat_index(expr: @ast::expr, base: @ast::expr) -> cmt {
        let base_cmt = self.cat_autoderef(expr, base);
        alt ty::index(self.tcx, base_cmt.ty) {
          some(mt) {
            // make deref of vectors explicit, as explained in the comment at
            // the head of this section
            let deref_lp = base_cmt.lp.map { |lp| @lp_deref(lp) };
            let deref_cmt = @{expr:expr, cat:cat_deref(base_cmt), lp:deref_lp,
                              mutbl:mt.mutbl, ty:mt.ty};
            let index_lp = deref_lp.map { |lp| @lp_index(lp) };
            @{expr:expr, cat:cat_index(deref_cmt), lp:index_lp,
              mutbl:mt.mutbl, ty:mt.ty}
          }
          none {
            self.tcx.sess.span_bug(
                expr.span,
                #fmt["Explicit index of non-index type `%s`",
                     ty_to_str(self.tcx, base_cmt.ty)]);
          }
        }
    }

    fn cat_def(expr: @ast::expr,
               expr_ty: ty::t,
               def: ast::def) -> cmt {
        alt def {
          ast::def_fn(_, _) | ast::def_mod(_) |
          ast::def_native_mod(_) | ast::def_const(_) |
          ast::def_use(_) | ast::def_variant(_, _) |
          ast::def_ty(_) | ast::def_prim_ty(_) |
          ast::def_ty_param(_, _) | ast::def_class(_) |
          ast::def_region(_) {
            @{expr:expr, cat:cat_rvalue(rv_static_item), lp:none,
              mutbl:m_imm, ty:expr_ty}
          }

          ast::def_arg(vid, mode) {
            let m = alt ty::resolved_mode(self.tcx, mode) {
              ast::by_mutbl_ref | ast::by_move | ast::by_copy { m_mutbl }
              ast::by_ref { m_const }
              ast::by_val { m_imm }
            };
            @{expr:expr, cat:cat_arg(vid), lp:some(@lp_arg(vid)),
              mutbl:m, ty:expr_ty}
          }

          ast::def_self(_) {
            @{expr:expr, cat:cat_rvalue(rv_self), lp:none,
              mutbl:m_imm, ty:expr_ty}
          }

          ast::def_upvar(upvid, inner, fn_node_id) {
            let ty = ty::node_id_to_type(self.tcx, fn_node_id);
            let proto = ty::ty_fn_proto(ty);
            alt proto {
              ast::proto_any | ast::proto_block {
                self.cat_def(expr, expr_ty, *inner)
              }
              ast::proto_bare | ast::proto_uniq | ast::proto_box {
                // FIXME #2152 allow mutation of moved upvars
                @{expr:expr, cat:cat_rvalue(rv_upvar), lp:none,
                  mutbl:m_imm, ty:expr_ty}
              }
            }
          }

          ast::def_local(vid, mutbl) {
            let m = if mutbl {m_mutbl} else {m_imm};
            @{expr:expr, cat:cat_local(vid), lp:some(@lp_local(vid)),
              mutbl:m, ty:expr_ty}
          }

          ast::def_binding(vid) {
            // no difference between a binding and any other local variable
            // from out point of view, except that they are always immutable
            @{expr:expr, cat:cat_local(vid), lp:some(@lp_local(vid)),
              mutbl:m_imm, ty:expr_ty}
          }
        }
    }

    fn cat_to_str(mutbl: str, cat: categorization) -> str {
        alt cat {
          cat_rvalue(rv_method) { "method" }
          cat_rvalue(rv_static_item) { "static item" }
          cat_rvalue(rv_upvar) { "upvar" }
          cat_rvalue(rv_misc) { "non-lvalue" }
          cat_rvalue(rv_self) { "self reference" }
          cat_deref(_) { mutbl + " dereference" }
          cat_field(_, _) { mutbl + " field" }
          cat_index(_) { mutbl + " vector/string contents" }
          cat_local(_) { mutbl + " local variable" }
          cat_arg(_) { mutbl + " argument" }
        }
    }

    fn cat_to_repr(cat: categorization) -> str {
        alt cat {
          cat_rvalue(rv_method) { "method" }
          cat_rvalue(rv_static_item) { "static_item" }
          cat_rvalue(rv_upvar) { "upvar" }
          cat_rvalue(rv_misc) { "rvalue" }
          cat_rvalue(rv_self) { "self" }
          cat_deref(cmt) { self.cat_to_repr(cmt.cat) + ".*" }
          cat_field(cmt, f) { self.cat_to_repr(cmt.cat) + "." + f }
          cat_index(cmt) { self.cat_to_repr(cmt.cat) + ".[]" }
          cat_local(node_id) { #fmt["local(%d)", node_id] }
          cat_arg(node_id) { #fmt["arg(%d)", node_id] }
        }
    }

    fn mut_to_str(mutbl: ast::mutability) -> str {
        alt mutbl {
          m_mutbl { "mutable" }
          m_const { "const" }
          m_imm { "immutable" }
        }
    }

    fn lp_to_str(lp: @loan_path) -> str {
        alt *lp {
          lp_local(node_id) { #fmt["local(%d)", node_id] }
          lp_arg(node_id) { #fmt["arg(%d)", node_id] }
          lp_deref(lp) { #fmt["%s.*", self.lp_to_str(lp)] }
          lp_field(lp, fld) { #fmt["%s.%s", self.lp_to_str(lp), fld] }
          lp_index(lp) { #fmt["%s.[]", self.lp_to_str(lp)] }
        }
    }

    fn cmt_to_repr(cmt: cmt) -> str {
        #fmt["{%s m:%s lp:%s ty:%s}",
             self.cat_to_repr(cmt.cat),
             self.mut_to_str(cmt.mutbl),
             cmt.lp.map_default("none", { |p| self.lp_to_str(p) }),
             ty_to_str(self.tcx, cmt.ty)]
    }

    fn cmt_to_str(cmt: cmt) -> str {
        let mut_str = self.mut_to_str(cmt.mutbl);
        self.cat_to_str(mut_str, cmt.cat)
    }

    fn bckerr_code_to_str(code: bckerr_code) -> str {
        alt code {
          err_mutbl(req, act) {
            #fmt["mutability mismatch, required %s but found %s",
                 self.mut_to_str(req), self.mut_to_str(act)]
          }
          err_mut_uniq {
            "unique value in aliasable, mutable location"
          }
          err_preserve_gc {
            "GC'd value would have to be preserved for longer \
                 than the scope of the function"
          }
        }
    }

    fn report_if_err(bres: bckres<()>) {
        alt bres {
          ok(()) { }
          err(e) { self.report(e); }
        }
    }

    fn report(err: bckerr) {
        self.tcx.sess.span_warn(
            err.cmt.expr.span,
            #fmt["Illegal borrow: %s",
                 self.bckerr_code_to_str(err.code)]);
    }
}

fn field_mutbl(tcx: ty::ctxt,
               base_ty: ty::t,
               f_name: str) -> option<ast::mutability> {
    // Need to refactor so that records/class fields can be treated uniformly.
    alt ty::get(base_ty).struct {
      ty::ty_rec(fields) {
        for fields.each { |f|
            if f.ident == f_name {
                ret some(f.mt.mutbl);
            }
        }
      }
      ty::ty_class(did, substs) {
        for ty::lookup_class_fields(tcx, did).each { |fld|
            if fld.ident == f_name {
                let m = alt fld.mutability {
                  ast::class_mutable { ast::m_mutbl }
                  ast::class_immutable { ast::m_imm }
                };
                ret some(m);
            }
        }
      }
      _ { }
    }

    ret none;
}

// ----------------------------------------------------------------------
// Preserve(Ex, S) holds if ToAddr(Ex) will remain valid for the entirety of
// the scope S.

enum preserve_ctxt = @{
    bccx: borrowck_ctxt, opt_scope_id: option<ast::node_id>
};

impl preserve_methods for borrowck_ctxt {
    fn preserve(cmt: cmt,
                opt_scope_id: option<ast::node_id>) -> bckres<()> {
        preserve_ctxt(@{bccx:self, opt_scope_id:opt_scope_id}).preserve(cmt)
    }
}

impl preserve_methods for preserve_ctxt {
    fn preserve(cmt: cmt) -> bckres<()> {
        let tcx = self.bccx.tcx;

        #debug["preserve(%s)", self.bccx.cmt_to_repr(cmt)];
        let _i = indenter();

        alt cmt.cat {
          cat_rvalue(_) {
            ok(())
          }
          cat_field(cmt_base, _) | cat_index(cmt_base) {
            self.preserve(cmt_base)
          }
          cat_local(vid) | cat_arg(vid) {
            // This should never happen.  Local variables are always lendable,
            // so either `loan()` should be called or there must be some
            // intermediate @ or &---they are not lendable but do not recurse.
            self.bccx.tcx.sess.span_bug(
                cmt.expr.span,
                "preserve() called with local or argument");
          }
          cat_deref(cmt1) {
            alt deref_kind(tcx, cmt1.ty) {
              uniqish {
                // Unique pointers: must be immutably rooted to a preserved
                // address.
                alt cmt1.mutbl {
                  m_mutbl | m_const { err({cmt:cmt, code:err_mut_uniq}) }
                  m_imm { self.preserve(cmt1) }
                }
              }

              abstractionish {
                // Abstraction-style pointers: they are stable if the value
                // being deref'd is stable
                self.preserve(cmt1)
              }

              regionish {
                // References are always "stable" by induction (when the
                // reference of type &MT was created, the memory must have
                // been stable)
                ok(())
              }

              unsafeish {
                // Unsafe pointers are the user's problem
                ok(())
              }

              gcish {
                // GC'd pointers of type @MT: always stable because we can inc
                // the ref count or keep a GC root as necessary.  We need to
                // insert this id into the root_map, however.
                alt self.opt_scope_id {
                  some(scope_id) {
                    self.bccx.root_map.insert(cmt.expr.id, scope_id);
                    ok(())
                  }
                  none {
                    err({cmt:cmt, code:err_preserve_gc})
                  }
                }
              }
            }
          }
        }
    }
}

// ----------------------------------------------------------------------
// Loan(Ex, M, S) = Ls holds if ToAddr(Ex) will remain valid for the entirety
// of the scope S, presuming that the returned set of loans `Ls` are honored.

type loan_ctxt = @{
    bccx: borrowck_ctxt,
    loans: @mut [loan]
};

impl loan_methods for borrowck_ctxt {
    fn loan(cmt: cmt,
            mutbl: ast::mutability) -> bckres<@const [loan]> {
        let lc = @{bccx: self, loans: @mut []};
        alt lc.loan(cmt, mutbl) {
          ok(()) { ok(lc.loans) }
          err(e) { err(e) }
        }
    }
}

impl loan_methods for loan_ctxt {
    fn ok_with_loan_of(cmt: cmt,
                       mutbl: ast::mutability) -> bckres<()> {
        // Note: all cmt's that we deal with will have a non-none lp, because
        // the entry point into this routine, `borrowck_ctxt::loan()`, rejects
        // any cmt with a none-lp.
        *self.loans += [{lp:option::get(cmt.lp),
                         cmt:cmt,
                         mutbl:mutbl}];
        ok(())
    }

    fn loan(cmt: cmt, req_mutbl: ast::mutability) -> bckres<()> {

        #debug["loan(%s, %s)",
               self.bccx.cmt_to_repr(cmt),
               self.bccx.mut_to_str(req_mutbl)];
        let _i = indenter();

        // see stable() above; should only be called when `cmt` is lendable
        if cmt.lp.is_none() {
            self.bccx.tcx.sess.span_bug(
                cmt.expr.span,
                "loan() called with non-lendable value");
        }

        alt cmt.cat {
          cat_rvalue(_) {
            self.bccx.tcx.sess.span_bug(
                cmt.expr.span,
                "rvalue with a non-none lp");
          }
          cat_field(cmt_base, _) | cat_index(cmt_base) {
            // if the field/array contents must be immutable, then the base
            // must also be immutable, or else the record/array as a whole
            // could be overwritten.  otherwise, though, const will suffice.
            let base_mutbl = alt req_mutbl {
              m_imm { m_imm }
              m_const | m_mutbl { m_const }
            };

            self.loan(cmt_base, base_mutbl).chain { |_ok|
                self.ok_with_loan_of(cmt, req_mutbl)
            }
          }
          cat_local(_) | cat_arg(_) {
            self.ok_with_loan_of(cmt, req_mutbl)
          }
          cat_deref(cmt1) {
            alt deref_kind(self.bccx.tcx, cmt1.ty) {
              uniqish {
                // Unique pointers: presuming that the base can be made
                // immutable, they are also uniquely tied to the stack frame.
                self.loan(cmt1, m_imm).chain { |_ok|
                    self.ok_with_loan_of(cmt, req_mutbl)
                }
              }

              abstractionish {
                // Abstraction "dereferences": these don't actually *do*
                // anything.
                self.loan(cmt1, req_mutbl).chain { |_ok|
                    self.ok_with_loan_of(cmt, req_mutbl)
                }
              }

              unsafeish | regionish | gcish {
                // Aliased data is not lendable.
                self.bccx.tcx.sess.span_bug(
                    cmt.expr.span,
                    "aliased ptr with a non-none lp");
              }
            }
          }
        }
    }
}
