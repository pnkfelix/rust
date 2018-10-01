// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use build::Builder;
use build::matches::{ProjectedAscriptions, MatchPair};
use hair::*;
use rustc::mir::*;
use std::u32;

impl<'a, 'gcx, 'tcx> Builder<'a, 'gcx, 'tcx> {
    pub fn field_match_pairs<'pat>(&mut self,
                                   place: Place<'tcx>,
                                   place_ascriptions: &ProjectedAscriptions<'tcx>,
                                   subpatterns: &'pat [FieldPattern<'tcx>])
                                   -> Vec<MatchPair<'pat, 'tcx>> {

        assert!(place_ascriptions.is_empty()); // FIXME bogus placeholder for real handling.

        subpatterns.iter()
                   .map(|fieldpat| {
                       let place = place.clone().field(fieldpat.field,
                                                       fieldpat.pattern.ty);
                       let ascriptions = place_ascriptions.field(fieldpat.field,
                                                                 fieldpat.pattern.ty);
                       MatchPair::new(place, &fieldpat.pattern, ascriptions)
                   })
                   .collect()
    }

    pub fn prefix_slice_suffix<'pat>(&mut self,
                                     match_pairs: &mut Vec<MatchPair<'pat, 'tcx>>,
                                     place: &Place<'tcx>,
                                     place_ascriptions: &ProjectedAscriptions<'tcx>,
                                     prefix: &'pat [Pattern<'tcx>],
                                     opt_slice: Option<&'pat Pattern<'tcx>>,
                                     suffix: &'pat [Pattern<'tcx>]) {
        let min_length = prefix.len() + suffix.len();
        assert!(min_length < u32::MAX as usize);
        let min_length = min_length as u32;

        assert!(place_ascriptions.is_empty()); // FIXME placeholder for actual handling

        match_pairs.extend(
            prefix.iter()
                  .enumerate()
                  .map(|(idx, subpattern)| {
                      let elem = ProjectionElem::ConstantIndex {
                          offset: idx as u32,
                          min_length,
                          from_end: false,
                      };
                      let ascriptions = place_ascriptions.elem(&elem);
                      let place = place.clone().elem(elem);
                      MatchPair::new(place, subpattern, ascriptions)
                  })
        );

        if let Some(subslice_pat) = opt_slice {
            let elem = ProjectionElem::Subslice {
                from: prefix.len() as u32,
                to: suffix.len() as u32
            };
            let subslice_ascriptions = place_ascriptions.elem(&elem);
            let subslice = place.clone().elem(elem);
            match_pairs.push(MatchPair::new(subslice, subslice_pat, subslice_ascriptions));
        }

        match_pairs.extend(
            suffix.iter()
                  .rev()
                  .enumerate()
                  .map(|(idx, subpattern)| {
                      let elem = ProjectionElem::ConstantIndex {
                          offset: (idx+1) as u32,
                          min_length,
                          from_end: true,
                      };
                      let ascriptions = place_ascriptions.elem(&elem);
                      let place = place.clone().elem(elem);
                      MatchPair::new(place, subpattern, ascriptions)
                  })
        );
    }
}

impl<'pat, 'tcx> MatchPair<'pat, 'tcx> {
    pub fn new(place: Place<'tcx>,
               pattern: &'pat Pattern<'tcx>,
               ascriptions: ProjectedAscriptions<'tcx>,
    ) -> MatchPair<'pat, 'tcx>
    {
        MatchPair {
            place,
            pattern,
            ascriptions,
            slice_len_checked: false,
        }
    }
}
