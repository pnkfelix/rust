// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::resolve;
use middle::typeck::check::method::LookupContext;
use middle::typeck::check::method::search;
use middle::typeck::check::method::search::push_candidates_from_impl;
use middle::typeck::check::method::search::MethodSearch;
use middle::typeck::check::method::search::RcvrType;
use middle::typeck::check::method::search::Candidate;

struct TraitMethods {
    candidates: ~[Candidate]
}

pub fn trait_methods(lookupcx: &LookupContext) -> TraitMethods {
    let trait_map: &mut resolve::TraitMap = &mut lookupcx.fcx.ccx.trait_map;
    let candidates = match trait_map.find(&lookupcx.expr.id) {
        None => { ~[] }
        Some(applicable_traits) => {
            let mut candidates = ~[];
            for applicable_traits.iter().advance |trait_did| {
                let opt_impl_infos = lookupcx.tcx().trait_impls.find(trait_did);
                for opt_impl_infos.iter().advance |impl_infos| {
                    for impl_infos.iter().advance |&impl_info| {
                        search::push_candidates_from_impl(
                            lookupcx, impl_info, &mut candidates);
                    }
                }
            }
            candidates
        }
    };
    TraitMethods {candidates: candidates}
}

impl MethodSearch for TraitMethods {
    fn push_candidates(&mut self,
                       lookupcx: &LookupContext,
                       rcvr_ty: &RcvrType,
                       out: &mut ~[Candidate]) {
        out.push_all(self.candidates);
    }
}

