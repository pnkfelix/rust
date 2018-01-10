// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::ty::{self, TyCtxt};
use rustc::session::Session;
use rustc::session::config::BorrowckMode;
use rustc_errors::{DiagnosticBuilder, DiagnosticId, Level};
use syntax_pos::{MultiSpan, Span};

use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Origin { Ast, Mir }

impl fmt::Display for Origin {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        // Certain `-Z borrowck=mode` modes force origin information into the diagnsotics. But most
        // (and importantly, the default mode) cause it to be left out.
        let mode = match ty::tls::with_opt(|opt_tcx| opt_tcx.map(|tcx| tcx.sess.borrowck_mode())) {
            Some(mode) => mode,
            None => return Ok(()),
        };
        match (mode, *self) {
            // `-Z borrowck=compare` means explicit annotate the source in all cases.
            (BorrowckMode::Compare, Origin::Mir) => write!(w, " (Mir)"),
            (BorrowckMode::Compare, Origin::Ast) => write!(w, " (Ast)"),

            // `-Z borrowck=sanity-check` means *note* cases where AST-borrowck would have errored
            // but new NLL regime does not.
            (BorrowckMode::SanityCheck, Origin::Ast) => write!(w, " (old lexical borrow error)"),

            // Otherwise print no origin info at all.
            _ => Ok(()),
        }
    }
}

impl Origin {
    /// Whether we should emit errors for the origin in the given mode
    pub fn should_emit_errors(self, mode: BorrowckMode) -> bool {
        match self {
            Origin::Ast => mode.use_ast(),
            Origin::Mir => mode.use_mir(),
        }
    }
}

pub trait BorrowckErrors {
    fn struct_span_err_with_code<'a, S: Into<MultiSpan>>(&'a self,
                                                         sp: S,
                                                         msg: &str,
                                                         code: DiagnosticId)
                                                         -> DiagnosticBuilder<'a>;

    fn struct_span_err<'a, S: Into<MultiSpan>>(&'a self,
                                               sp: S,
                                               msg: &str)
                                               -> DiagnosticBuilder<'a>;

    fn sess(&self) -> &Session;

    /// Downgrade the given error to warning or cancel entirely if we
    /// shouldn't emit it for a given origin in the current mode.
    ///
    /// Always make sure that the error gets passed through this function
    /// before you return it.
    fn downgrade_based_on_origin<'a>(&'a self,
                                     mut diag: DiagnosticBuilder<'a>,
                                     o: Origin)
                                     -> DiagnosticBuilder<'a> {
        let mode = self.sess().borrowck_mode();
        debug!("downgrade_based_on_origin mode: {:?} diag: {:?} o: {:?}", mode, diag, o);
        match o {
            Origin::Ast => {
                // remember that we saw this (if migrating and its serious)
                match diag.level {
                    Level::Bug | Level::Fatal | Level::PhaseFatal | Level::Error => {
                        self.sess().seen_ast_borrowck_errors.set(true);
                    }
                    Level::Warning | Level::Note | Level::Help | Level::Cancelled =>  {}
                }
                // cancel it if we are in or migrating to MIR-borrowck.
                match mode {
                    BorrowckMode::Ast |
                    BorrowckMode::Compare => {} // no downgrade
                    BorrowckMode::Mir |
                    BorrowckMode::Migrate => {
                        // cancel, but remember that it happened. FIXME
                        self.sess().diagnostic().cancel(&mut diag);
                    }
                    BorrowckMode::SanityCheck => {
                        // cancel, but remember that it happened.
                        let mut delayed = self.sess().delayed_ast_borrowck_errors.borrow_mut();
                        delayed.push((*diag).clone());
                        self.sess().diagnostic().cancel(&mut diag);
                    }
                }
            }
            Origin::Mir => {
                match mode {
                    BorrowckMode::Ast => { // old-style: always downgrade to fully cancelled
                        self.sess().diagnostic().cancel(&mut diag);
                    }

                    BorrowckMode::Mir |
                    BorrowckMode::Compare => {} // no downgrade

                    BorrowckMode::Migrate |
                    BorrowckMode::SanityCheck => { // conditionally downgrade to warning
                        if !self.sess().seen_ast_borrowck_errors.get() {
                            self.sess().diagnostic().downgrade_to_warning(&mut diag);
                            diag.warn("This code may have been previously accepted by the compiler \
                                       but it is being phased out; \
                                       it will become a hard error in a future release!");
                            diag.note("For more information, see \
                                       https://github.com/rust-lang/rust/issues/43234");
                        }
                    }
                }
            }
        }
        diag
    }

    fn cannot_move_when_borrowed(&self, span: Span, desc: &str, o: Origin)
                                 -> DiagnosticBuilder<'_>
    {
        let err = struct_span_err!(self, span, E0505,
                                   "cannot move out of `{}` because it is borrowed{OGN}",
                                   desc, OGN=o);
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_use_when_mutably_borrowed(&self,
                                        span: Span,
                                        desc: &str,
                                        borrow_span: Span,
                                        borrow_desc: &str,
                                        o: Origin)
                                        -> DiagnosticBuilder<'_>
    {
        let mut err = struct_span_err!(self, span, E0503,
                         "cannot use `{}` because it was mutably borrowed{OGN}",
                         desc, OGN=o);

        err.span_label(borrow_span, format!("borrow of `{}` occurs here", borrow_desc));
        err.span_label(span, format!("use of borrowed `{}`", borrow_desc));

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_act_on_uninitialized_variable(&self,
                                            span: Span,
                                            verb: &str,
                                            desc: &str,
                                            o: Origin)
                                            -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0381,
                                   "{} of possibly uninitialized variable: `{}`{OGN}",
                                   verb, desc, OGN=o);
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_mutably_borrow_multiply(&self,
                                      new_loan_span: Span,
                                      desc: &str,
                                      opt_via: &str,
                                      old_loan_span: Span,
                                      old_opt_via: &str,
                                      old_load_end_span: Option<Span>,
                                      o: Origin)
                                      -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, new_loan_span, E0499,
                         "cannot borrow `{}`{} as mutable more than once at a time{OGN}",
                         desc, opt_via, OGN=o);
        if old_loan_span == new_loan_span {
            // Both borrows are happening in the same place
            // Meaning the borrow is occurring in a loop
            err.span_label(new_loan_span,
                           format!("mutable borrow starts here in previous \
                                    iteration of loop{}", opt_via));
            if let Some(old_load_end_span) = old_load_end_span {
                err.span_label(old_load_end_span, "mutable borrow ends here");
            }
        } else {
            err.span_label(old_loan_span,
                           format!("first mutable borrow occurs here{}", old_opt_via));
            err.span_label(new_loan_span,
                           format!("second mutable borrow occurs here{}", opt_via));
            if let Some(old_load_end_span) = old_load_end_span {
                err.span_label(old_load_end_span, "first borrow ends here");
            }
        }
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_uniquely_borrow_by_two_closures(&self,
                                              new_loan_span: Span,
                                              desc: &str,
                                              old_loan_span: Span,
                                              old_load_end_span: Option<Span>,
                                              o: Origin)
                                              -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, new_loan_span, E0524,
                         "two closures require unique access to `{}` at the same time{OGN}",
                         desc, OGN=o);
        err.span_label(
            old_loan_span,
            "first closure is constructed here");
        err.span_label(
            new_loan_span,
            "second closure is constructed here");
        if let Some(old_load_end_span) = old_load_end_span {
            err.span_label(
                old_load_end_span,
                "borrow from first closure ends here");
        }
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_uniquely_borrow_by_one_closure(&self,
                                             new_loan_span: Span,
                                             desc_new: &str,
                                             opt_via: &str,
                                             old_loan_span: Span,
                                             noun_old: &str,
                                             old_opt_via: &str,
                                             previous_end_span: Option<Span>,
                                             o: Origin)
                                             -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, new_loan_span, E0500,
                         "closure requires unique access to `{}` but {} is already borrowed{}{OGN}",
                         desc_new, noun_old, old_opt_via, OGN=o);
        err.span_label(new_loan_span,
                       format!("closure construction occurs here{}", opt_via));
        err.span_label(old_loan_span,
                       format!("borrow occurs here{}", old_opt_via));
        if let Some(previous_end_span) = previous_end_span {
            err.span_label(previous_end_span, "borrow ends here");
        }
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_reborrow_already_uniquely_borrowed(&self,
                                                 new_loan_span: Span,
                                                 desc_new: &str,
                                                 opt_via: &str,
                                                 kind_new: &str,
                                                 old_loan_span: Span,
                                                 old_opt_via: &str,
                                                 previous_end_span: Option<Span>,
                                                 o: Origin)
                                                 -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, new_loan_span, E0501,
                         "cannot borrow `{}`{} as {} because previous closure \
                          requires unique access{OGN}",
                         desc_new, opt_via, kind_new, OGN=o);
        err.span_label(new_loan_span,
                       format!("borrow occurs here{}", opt_via));
        err.span_label(old_loan_span,
                       format!("closure construction occurs here{}", old_opt_via));
        if let Some(previous_end_span) = previous_end_span {
            err.span_label(previous_end_span, "borrow from closure ends here");
        }
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_reborrow_already_borrowed(&self,
                                        span: Span,
                                        desc_new: &str,
                                        msg_new: &str,
                                        kind_new: &str,
                                        old_span: Span,
                                        noun_old: &str,
                                        kind_old: &str,
                                        msg_old: &str,
                                        old_load_end_span: Option<Span>,
                                        o: Origin)
                                        -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, span, E0502,
                         "cannot borrow `{}`{} as {} because {} is also borrowed as {}{}{OGN}",
                         desc_new, msg_new, kind_new, noun_old, kind_old, msg_old, OGN=o);
        err.span_label(span, format!("{} borrow occurs here{}", kind_new, msg_new));
        err.span_label(old_span, format!("{} borrow occurs here{}", kind_old, msg_old));
        if let Some(old_load_end_span) = old_load_end_span {
            err.span_label(old_load_end_span, format!("{} borrow ends here", kind_old));
        }
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_assign_to_borrowed(&self, span: Span, borrow_span: Span, desc: &str, o: Origin)
                                 -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, span, E0506,
                         "cannot assign to `{}` because it is borrowed{OGN}",
                         desc, OGN=o);

        err.span_label(borrow_span, format!("borrow of `{}` occurs here", desc));
        err.span_label(span, format!("assignment to borrowed `{}` occurs here", desc));

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_move_into_closure(&self, span: Span, desc: &str, o: Origin)
                                -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0504,
                                   "cannot move `{}` into closure because it is borrowed{OGN}",
                                   desc, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_reassign_immutable(&self, span: Span, desc: &str, o: Origin)
                                 -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0384,
                                   "cannot assign twice to immutable variable `{}`{OGN}",
                                   desc, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_assign(&self, span: Span, desc: &str, o: Origin) -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0594,
                                  "cannot assign to {}{OGN}",
                                  desc, OGN=o);
        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_assign_static(&self, span: Span, desc: &str, o: Origin)
                            -> DiagnosticBuilder
    {
        self.cannot_assign(span, &format!("immutable static item `{}`", desc), o)
    }

    fn cannot_move_out_of(&self, move_from_span: Span, move_from_desc: &str, o: Origin)
                          -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, move_from_span, E0507,
                                       "cannot move out of {}{OGN}",
                                       move_from_desc, OGN=o);
        err.span_label(
            move_from_span,
            format!("cannot move out of {}", move_from_desc));

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_move_out_of_interior_noncopy(&self,
                                           move_from_span: Span,
                                           ty: ty::Ty,
                                           is_index: bool,
                                           o: Origin)
                                           -> DiagnosticBuilder
    {
        let type_name = match (&ty.sty, is_index) {
            (&ty::TyArray(_, _), true) => "array",
            (&ty::TySlice(_),    _) => "slice",
            _ => span_bug!(move_from_span, "this path should not cause illegal move"),
        };
        let mut err = struct_span_err!(self, move_from_span, E0508,
                                       "cannot move out of type `{}`, \
                                        a non-copy {}{OGN}",
                                       ty, type_name, OGN=o);
        err.span_label(move_from_span, "cannot move out of here");

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_move_out_of_interior_of_drop(&self,
                                           move_from_span: Span,
                                           container_ty: ty::Ty,
                                           o: Origin)
                                           -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, move_from_span, E0509,
                                       "cannot move out of type `{}`, \
                                        which implements the `Drop` trait{OGN}",
                                       container_ty, OGN=o);
        err.span_label(move_from_span, "cannot move out of here");

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_act_on_moved_value(&self,
                                 use_span: Span,
                                 verb: &str,
                                 optional_adverb_for_moved: &str,
                                 moved_path: &str,
                                 o: Origin)
                                 -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, use_span, E0382,
                                   "{} of {}moved value: `{}`{OGN}",
                                   verb, optional_adverb_for_moved, moved_path, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_partially_reinit_an_uninit_struct(&self,
                                                span: Span,
                                                uninit_path: &str,
                                                o: Origin)
                                                -> DiagnosticBuilder
    {
        let err = struct_span_err!(self,
                                   span,
                                   E0383,
                                   "partial reinitialization of uninitialized structure `{}`{OGN}",
                                   uninit_path, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn closure_cannot_assign_to_borrowed(&self,
                                         span: Span,
                                         descr: &str,
                                         o: Origin)
                                         -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0595, "closure cannot assign to {}{OGN}",
                                   descr, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_borrow_path_as_mutable(&self,
                                     span: Span,
                                     path: &str,
                                     o: Origin)
                                     -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0596, "cannot borrow {} as mutable{OGN}",
                                   path, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_borrow_across_generator_yield(&self,
                                            span: Span,
                                            yield_span: Span,
                                            o: Origin)
                                            -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self,
                                       span,
                                       E0626,
                                       "borrow may still be in use when generator yields{OGN}",
                                       OGN=o);
        err.span_label(yield_span, "possible yield occurs here");

        self.downgrade_based_on_origin(err, o)
    }

    fn path_does_not_live_long_enough(&self,
                                      span: Span,
                                      path: &str,
                                      o: Origin)
                                      -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0597, "{} does not live long enough{OGN}",
                                   path, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn lifetime_too_short_for_reborrow(&self,
                                       span: Span,
                                       path: &str,
                                       o: Origin)
                                       -> DiagnosticBuilder
    {
        let err = struct_span_err!(self, span, E0598,
                                   "lifetime of {} is too short to guarantee \
                                    its contents can be safely reborrowed{OGN}",
                                   path, OGN=o);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_act_on_capture_in_sharable_fn(&self,
                                            span: Span,
                                            bad_thing: &str,
                                            help: (Span, &str),
                                            o: Origin)
                                            -> DiagnosticBuilder
    {
        let (help_span, help_msg) = help;
        let mut err = struct_span_err!(self, span, E0387,
                                       "{} in a captured outer variable in an `Fn` closure{OGN}",
                                       bad_thing, OGN=o);
        err.span_help(help_span, help_msg);

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_assign_into_immutable_reference(&self,
                                              span: Span,
                                              bad_thing: &str,
                                              o: Origin)
                                              -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, span, E0389, "{} in a `&` reference{OGN}",
                                       bad_thing, OGN=o);
        err.span_label(span, "assignment into an immutable reference");

        self.downgrade_based_on_origin(err, o)
    }

    fn cannot_capture_in_long_lived_closure(&self,
                                            closure_span: Span,
                                            borrowed_path: &str,
                                            capture_span: Span,
                                            o: Origin)
                                            -> DiagnosticBuilder
    {
        let mut err = struct_span_err!(self, closure_span, E0373,
                                       "closure may outlive the current function, \
                                        but it borrows {}, \
                                        which is owned by the current function{OGN}",
                                       borrowed_path, OGN=o);
        err.span_label(capture_span, format!("{} is borrowed here", borrowed_path))
            .span_label(closure_span, format!("may outlive borrowed value {}", borrowed_path));

        self.downgrade_based_on_origin(err, o)
    }
}

impl<'b, 'gcx, 'tcx> BorrowckErrors for TyCtxt<'b, 'gcx, 'tcx> {
    fn struct_span_err_with_code<'a, S: Into<MultiSpan>>(&'a self,
                                                         sp: S,
                                                         msg: &str,
                                                         code: DiagnosticId)
                                                         -> DiagnosticBuilder<'a>
    {
        self.sess.struct_span_err_with_code(sp, msg, code)
    }

    fn struct_span_err<'a, S: Into<MultiSpan>>(&'a self,
                                               sp: S,
                                               msg: &str)
                                               -> DiagnosticBuilder<'a>
    {
        self.sess.struct_span_err(sp, msg)
    }

    fn sess(&self) -> &Session {
        self.sess
    }
}
