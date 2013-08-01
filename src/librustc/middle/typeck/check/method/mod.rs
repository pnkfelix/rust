// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::ty;
use middle::typeck::infer;
use middle::typeck::check::FnCtxt;
use middle::typeck::check::DerefArgs;
use middle::typeck::method_map_entry;
use syntax::ast;
use util::ppaux::Repr;

pub mod doc;
pub mod inherent;
pub mod traits;
pub mod search;
pub mod report;

type MethodResult<T> = Result<T, ()>;

pub struct LookupContext<'self> {
    fcx: @mut FnCtxt,
    expr: @ast::expr,
    self_expr: @ast::expr,
    callee_id: ast::node_id,
    m_name: ast::ident,
    supplied_tps: &'self [ty::t],
    deref_args: DerefArgs,
    check_traits: CheckTraitsFlag,
    autoderef_receiver: AutoderefReceiverFlag,
}

pub enum AutoderefReceiverFlag {
    AutoderefReceiver,
    DontAutoderefReceiver,
}

pub enum CheckTraitsFlag {
    CheckTraitsOnly,
    CheckTraitsAndInherentMethods,
}

pub fn lookup(
        fcx: @mut FnCtxt,

        // In a call `a.b::<X, Y, ...>(...)`:
        expr: @ast::expr,                   // The expression `a.b(...)`.
        self_expr: @ast::expr,              // The expression `a`.
        callee_id: ast::node_id,            /* Where to store `a.b`'s type,
                                             * also the scope of the call */
        m_name: ast::ident,                 // The ident `b`.
        self_ty: ty::t,                     // The type of `a`.
        supplied_tps: &[ty::t],             // The list of types X, Y, ... .
        deref_args: DerefArgs,              // Whether we autopointer first.
        check_traits: CheckTraitsFlag,      // Whether we check traits only.
        autoderef_receiver: AutoderefReceiverFlag)
        -> MethodResult<method_map_entry> {
    let lookupcx = LookupContext {
        fcx: fcx,
        expr: expr,
        self_expr: self_expr,
        callee_id: callee_id,
        m_name: m_name,
        supplied_tps: supplied_tps,
        deref_args: deref_args,
        check_traits: check_traits,
        autoderef_receiver: autoderef_receiver,
    };
    return lookupcx.lookup(self_ty);
}

impl<'self> LookupContext<'self> {
    fn lookup(&self, self_ty: ty::t) {
        match self.check_traits {
            CheckTraitsOnly => {}
            CheckTraitsAndInherentMethods => {
                match self.do_search(self_ty, inherent::InherentMethods) {
                    Ok(r) => {
                        return Ok(r);
                    }
                    Err(NoMethodFound) => {}
                    Err(e) => {
                        self.report(e);
                        return Err(());
                    }
                }
            }
        }

        let trait_methods = traits::trait_methods(self);
        return match self.do_search(self_ty, trait_methods) {
            Ok(r) => {
                Ok(r)
            }
            Err(e) => {
                self.report(e);
                Err(())
            }
        };
    }

    fn tcx(&self) -> ty::ctxt {
        self.fcx.tcx()
    }

    fn infcx(&self) -> @mut infer::InferCtxt {
        self.fcx.infcx
    }
}

pub fn get_mode_from_explicit_self(explicit_self: ast::explicit_self_)
                                   -> ty::SelfMode {
    match explicit_self {
        sty_value => ty::ByRef,
        _ => ty::ByCopy,
    }
}
