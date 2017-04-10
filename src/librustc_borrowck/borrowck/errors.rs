use borrowck::BorrowckCtxt;

use errors::DiagnosticBuilder;
use syntax_pos::Span;

use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Origin { Ast, Mir }

impl fmt::Display for Origin {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, w)
    }
}

impl<'a, 'tcx> BorrowckCtxt<'a, 'tcx> {
    pub(crate) fn cannot_move_when_borrowed(&self, span: Span, desc: &str, o: Origin)
                                            -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0505,
                         "cannot move out of `{}` becauase it is borrowed ({})",
                         desc, o)
    }

    pub(crate) fn cannot_use_when_mutably_borrowed(&self, span: Span, desc: &str, o: Origin)
                                                   -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0503,
                         "cannot use `{}` because it was mutably borrowed ({})",
                         desc, o)
    }

    pub(crate) fn cannot_act_on_uninitialized_variable(&self,
                                                       span: Span,
                                                       verb: &str,
                                                       desc: &str,
                                                       o: Origin)
                                                       -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0381,
                         "{} of possibly uninitialized variable: `{}` ({})",
                         verb, desc, o)
    }

    pub(crate) fn cannot_mutably_borrow_multiply(&self,
                                                 span: Span,
                                                 desc: &str,
                                                 opt_via: &str,
                                                 o: Origin)
                                                 -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0499,
                         "cannot borrow `{}`{} as mutable more than once at a time ({})",
                         desc, opt_via, o)
    }

    pub(crate) fn cannot_uniquely_borrow_by_two_closures(&self, span: Span, desc: &str, o: Origin)
                                                         -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0524,
                         "two closures require unique access to `{}` at the same time ({})",
                         desc, o)
    }

    pub(crate) fn cannot_uniquely_borrow_by_one_closure(&self,
                                                        span: Span,
                                                        desc_new: &str,
                                                        noun_old: &str,
                                                        msg_old: &str,
                                                        o: Origin)
                                                        -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0500,
                         "closure requires unique access to `{}` but {} is already borrowed{} ({})",
                         desc_new, noun_old, msg_old, o)
    }

    pub(crate) fn cannot_reborrow_already_uniquely_borrowed(&self,
                                                            span: Span,
                                                            desc_new: &str,
                                                            msg_new: &str,
                                                            kind_new: &str,
                                                            o: Origin)
                                                            -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0501,
                         "cannot borrow `{}`{} as {} because previous closure \
                          requires unique access ({})",
                         desc_new, msg_new, kind_new, o)
    }

    pub(crate) fn cannot_reborrow_already_borrowed(&self,
                                                   span: Span,
                                                   desc_new: &str,
                                                   msg_new: &str,
                                                   kind_new: &str,
                                                   noun_old: &str,
                                                   kind_old: &str,
                                                   msg_old: &str,
                                                   o: Origin)
                                                   -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0502,
                         "cannot borrow `{}`{} as {} because {} is also borrowed as {}{} ({})",
                         desc_new, msg_new, kind_new, noun_old, kind_old, msg_old, o)
    }

    pub(crate) fn cannot_assign_to_borrowed(&self, span: Span, desc: &str, o: Origin)
                                            -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0506,
                         "cannot assign to `{}` because it is borrowed ({})",
                         desc, o)
    }

    pub(crate) fn cannot_move_into_closure(&self, span: Span, desc: &str, o: Origin)
                                           -> DiagnosticBuilder
    {
        struct_span_err!(self, span, E0504,
                         "cannot move `{}` into closure because it is borrowed ({})",
                         desc, o)
    }
}
