// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod doc;
mod inherent;
mod traits;

type MethodResult<T> = Result<T, ()>;

pub fn lookup(
        fcx: @mut FnCtxt,

        // In a call `a.b::<X, Y, ...>(...)`:
        expr: @ast::expr,                   // The expression `a.b(...)`.
        self_expr: @ast::expr,              // The expression `a`.
        callee_id: node_id,                 /* Where to store `a.b`'s type,
                                             * also the scope of the call */
        m_name: ast::ident,                 // The ident `b`.
        self_ty: ty::t,                     // The type of `a`.
        supplied_tps: &[ty::t],             // The list of types X, Y, ... .
        deref_args: check::DerefArgs,       // Whether we autopointer first.
        check_traits: CheckTraitsFlag,      // Whether we check traits only.
        autoderef_receiver: AutoderefReceiverFlag)
        -> MethodResult<method_map_entry> {
    let impl_dups = @mut HashSet::new();
    let lcx = LookupContext {
        fcx: fcx,
        expr: expr,
        self_expr: self_expr,
        callee_id: callee_id,
        m_name: m_name,
        supplied_tps: supplied_tps,
        impl_dups: impl_dups,
        inherent_candidates: @mut ~[],
        extension_candidates: @mut ~[],
        deref_args: deref_args,
        check_traits: check_traits,
        autoderef_receiver: autoderef_receiver,
    };
    let mme = lcx.do_lookup(self_ty);
    debug!("method lookup for %s yielded %?", expr.repr(fcx.tcx()), mme);
    return mme;
}

pub struct LookupContext<'self> {
    fcx: @mut FnCtxt,
    expr: @ast::expr,
    self_expr: @ast::expr,
    callee_id: node_id,
    m_name: ast::ident,
    supplied_tps: &'self [ty::t],
    impl_dups: @mut HashSet<def_id>,
    inherent_candidates: @mut ~[Candidate],
    extension_candidates: @mut ~[Candidate],
    deref_args: check::DerefArgs,
    check_traits: CheckTraitsFlag,
    autoderef_receiver: AutoderefReceiverFlag,
}

