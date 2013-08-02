use middle::ty;
use middle::typeck::check::method;
use middle::typeck::check::method::search::*;
use middle::typeck::method_origin;
use middle::typeck::method_param;
use middle::typeck::method_static;
use middle::typeck::method_self;
use middle::typeck::method_super;
use middle::typeck::method_trait;
use std::uint;
use syntax::ast;
use syntax::ast_map;

impl<'self> method::LookupContext<'self> {
    fn report(&self, err: SearchError) {
        let tcx = self.fcx.tcx();
        match err {
            NoMethodFound => {
                tcx.sess.span_err(
                    self.expr.span,
                    "multiple applicable methods in scope");
            }

            IncorrectNumberOfTypeParameters(0, _) => {
                tcx.sess.span_err(
                    self.expr.span,
                    "this method does not take type parameters");
            }

            IncorrectNumberOfTypeParameters(expected, actual) => {
                tcx.sess.span_err(
                    self.expr.span,
                    "incorrect number of type \
                     parameters given for this method: \
                     expected %d, found %d",
                    expected, actual);
            }

            StaticMethodCalled => {
                tcx.sess.span_err(
                    self.expr.span,
                    "method syntax used for fn with no `self` declaration");
            }

            NotManaged => {
                tcx.sess.span_err(
                    self.expr.span,
                    "`@self` method invoked but receiver is not a managed box");
            }

            NotOwned => {
                tcx.sess.span_err(
                    self.expr.span,
                    "`~self` method invoked but receiver is not an owned box");
            }

            UnsizedReceiverWithByValueMethod => {
                tcx.sess.span_err(
                    self.expr.span,
                    "cannot call a by-value with an unsized receiver");
            }

            ObjectMethodReferencingSelf => {
                tcx.sess.span_err(
                    self.expr.span,
                    "cannot call a method referencing the `Self` type \
                     with an object receiver");
            }

            ObjectMethodGeneric => {
                tcx.sess.span_err(
                    self.expr.span,
                    "cannot call a generic method \
                     with an object receiver");
            }

            DropTraitMethod => {
                tcx.sess.span_err(
                    self.expr.span,
                    "explicit call to destructor");
            }

            ExpectedFound(expected, actual, err) => {
                self.fcx.infcx.report_mismatched_types(
                    self.expr.span,
                    expected,
                    actual,
                    err);
            }

            MultipleCandidates(ref candidates) => {
                tcx.sess.span_err(
                    self.expr.span,
                    "multiple applicable methods in scope");
                for uint::range(0, candidates.len()) |idx| {
                    self.report_candidate(idx, &candidates[idx].origin);
                }
            }
        }
    }

    fn report_candidate(&self, idx: uint, origin: &method_origin) {
        match *origin {
            method_static(impl_did) => {
                self.report_static_candidate(idx, impl_did)
            }
            method_param(ref mp) => {
                self.report_param_candidate(idx, (*mp).trait_id)
            }
            method_trait(trait_did, _, _) |
            method_self(trait_did, _) |
            method_super(trait_did, _) => {
                self.report_trait_candidate(idx, trait_did)
            }
        }
    }

    fn report_static_candidate(&self, idx: uint, did: ast::def_id) {
        let span = if did.crate == ast::local_crate {
            match self.tcx().items.find(&did.node) {
                Some(&ast_map::node_method(m, _, _)) => m.span,
                _ => fail!("report_static_candidate: bad item %?", did)
            }
        } else {
            self.expr.span
        };
        self.tcx().sess.span_note(
            span,
            fmt!("candidate #%u is `%s`",
                 (idx+1u),
                 ty::item_path_str(self.tcx(), did)));
    }

    fn report_param_candidate(&self, idx: uint, did: ast::def_id) {
        self.tcx().sess.span_note(
            self.expr.span,
            fmt!("candidate #%u derives from the bound `%s`",
                 (idx+1u),
                 ty::item_path_str(self.tcx(), did)));
    }

    fn report_trait_candidate(&self, idx: uint, did: ast::def_id) {
        self.tcx().sess.span_note(
            self.expr.span,
            fmt!("candidate #%u derives from the type of the receiver, \
                  which is the trait `%s`",
                 (idx+1u),
                 ty::item_path_str(self.tcx(), did)));
    }
}