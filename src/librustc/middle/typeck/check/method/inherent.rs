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
use middle::typeck::{method_param, method_self, method_super, method_trait};
use middle::typeck::check::method;
use middle::typeck::check::method::LookupContext;
use middle::typeck::check::method::search;
use middle::typeck::check::method::search::push_candidates_from_impl;
use middle::typeck::check::method::search::MethodSearch;
use middle::typeck::check::method::search::RcvrType;
use middle::typeck::check::method::search::Candidate;
use syntax::ast;

pub struct InherentMethods;

impl MethodSearch for InherentMethods {
    fn push_candidates(&mut self,
                       lookupcx: &method::LookupContext,
                       rcvr_ty: &RcvrType,
                       out: &mut ~[Candidate]) {
        match *rcvr_ty {
            search::SizedType(t) => {
                lookupcx.push_candidates_from_sized_type(t, out)
            }

            search::ExistentialType(def_id, ref substs) => {
                lookupcx.push_candidates_from_object(def_id, substs, out)
            }

            search::VectorType(_) | search::StringType => {}
        }
    }
}

impl<'self> method::LookupContext<'self> {
    fn push_candidates_from_sized_type(&self,
                                       rcvr_ty: ty::t,
                                       out: &mut ~[Candidate]) {
        debug!("push_candidates_from_sized_type(rcvr_ty=%s)",
               rcvr_ty.repr(self.tcx()));

        match ty::get(rcvr_ty).sty {
            ty::ty_param(param_ty) => {
                self.push_param_bounds(param_ty, out);
            }

            ty::ty_self(self_did) => {
                // Call is of the form "self.foo()" and appears in one
                // of a trait's default method implementations.
                let substs = ty::substs {
                    self_r: None,
                    self_ty: None,
                    tps: ~[]
                };
                self.push_self_bounds(self_did, &substs, out);
            }

            ty::ty_enum(did, _) | ty::ty_struct(did, _) => {
                self.push_inherent_impls(did, out);
            }
        }
    }

    fn push_param_bounds(&self,
                         param_ty: ty::param_ty,
                         out: &mut ~[Candidate]) {
        let tcx = self.tcx();
        let mut next_bound_idx = 0; // count only trait bounds
        let type_param_def = match tcx.ty_param_defs.find(&param_ty.def_id.node) {
            Some(t) => t,
            None => {
                tcx.sess.span_bug(
                    self.expr.span,
                    fmt!("No param def for %?", param_ty));
            }
        };

        for ty::each_bound_trait_and_supertraits(tcx, type_param_def.bounds)
            |bound_trait_ref|
        {
            let this_bound_idx = next_bound_idx;
            next_bound_idx += 1;

            let trait_methods = ty::trait_methods(tcx, bound_trait_ref.def_id);
            let pos = {
                match trait_methods.iter().position(
                    |m| m.ident == self.m_name)
                {
                    Some(pos) => pos,
                    None => {
                        debug!("trait doesn't contain method: %?",
                               bound_trait_ref.def_id);
                        loop; // check next trait or bound
                    }
                }
            };
            let method = trait_methods[pos];

            let cand = Candidate {
                rcvr_substs: bound_trait_ref.substs.clone(),
                method_ty: method,
                origin: method_param(
                    method_param {
                        trait_id: bound_trait_ref.def_id,
                        method_num: pos,
                        param_num: param_ty.idx,
                        bound_num: this_bound_idx,
                    })
            };

            debug!("pushing inherent candidate for param: %s", cand.repr(tcx));
            out.push(cand);
        }
    }

    fn push_self_bounds(&self,
                        did: ast::def_id,
                        substs: &ty::substs,
                        out: &mut ~[Candidate]) {
        struct MethodInfo {
            method_ty: @ty::Method,
            trait_def_id: ast::def_id,
            index: uint
        }

        let tcx = self.tcx();

        // First, try self methods
        let mut method_info: Option<MethodInfo> = None;
        let methods = ty::trait_methods(tcx, did);
        match methods.iter().position(|m| m.ident == self.m_name) {
            Some(i) => {
                method_info = Some(MethodInfo {
                    method_ty: methods[i],
                    index: i,
                    trait_def_id: did
                });
            }
            None => ()
        }

        // No method found yet? Check each supertrait
        if method_info.is_none() {
            for ty::trait_supertraits(tcx, did).iter().advance |trait_ref| {
                let supertrait_methods =
                    ty::trait_methods(tcx, trait_ref.def_id);
                match supertrait_methods.iter().position(
                    |m| m.ident == self.m_name)
                {
                    Some(i) => {
                        method_info = Some(MethodInfo {
                            method_ty: supertrait_methods[i],
                            index: i,
                            trait_def_id: trait_ref.def_id
                        });
                        break;
                    }
                    None => ()
                }
            }
        }

        match method_info {
            Some(ref info) => {
                // We've found a method -- return it
                let self_ty = ty::mk_self(self.tcx(), did);
                let rcvr_substs = ty::substs {self_ty: Some(self_ty),
                                              ..substs.clone()};
                let origin = if did == info.trait_def_id {
                    method_self(info.trait_def_id, info.index)
                } else {
                    method_super(info.trait_def_id, info.index)
                };
                out.push(Candidate {
                    rcvr_substs: rcvr_substs,
                    method_ty: info.method_ty,
                    origin: origin
                });
            }
            _ => return
        }
    }

    fn push_inherent_impls(&self,
                           did: ast::def_id,
                           out: &mut ~[Candidate]) {
        let opt_impl_infos = self.tcx().inherent_impls.find(&did);
        for opt_impl_infos.iter().advance |impl_infos| {
            for impl_infos.iter().advance |&impl_info| {
                search::push_candidates_from_impl(self, impl_info, out);
            }
        }
    }

    fn push_candidates_from_object(&self,
                                   did: ast::def_id,
                                   substs: &ty::substs,
                                   out: &mut ~[Candidate]) {
        debug!("push_candidates_from_object(did=%s, substs=%s)",
               did.repr(self.tcx()),
               substs.repr(self.tcx()));

        let tcx = self.tcx();
        let ms = ty::trait_methods(tcx, did);
        let index = match ms.iter().position(|m| m.ident == self.m_name) {
            Some(i) => i,
            None => { return; } // no method with the right name
        };
        let method = ms[index];

        out.push(Candidate {
            rcvr_substs: substs.clone(),
            method_ty: method,
            origin: method_trait(did, index),
        });
    }
}
