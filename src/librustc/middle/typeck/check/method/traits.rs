// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

struct TraitMethods {
    tcx: ty::ctxt,
    opt_applicable_traits: Option<@mut ~[def_id]>
}

impl MethodSearch for TraitMethods {
    fn push_candidates(&mut self, rcvr_ty: &RcvrType, out: &mut [Candidate]) {
        let applicable_traits = match self.opt_applicable_traits {
            Some(applicable_traits) => { applicable_traits }
            None => { return; }
        };

        for applicable_traits.iter().advance |trait_did| {
            let opt_impl_infos = self.tcx().trait_impls.find(trait_did);
            for opt_impl_infos.iter().advance |impl_infos| {
                for impl_infos.iter().advance |impl_info| {
                    self.push_candidates_from_impl(
                        self.extension_candidates, *impl_info);
                }
            }
        }
    }
}

