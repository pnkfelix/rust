// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// compile-flags: -Z identify_regions
// ignore-tidy-linelength

// Binding the borrow's subject outside the loop does not increase the
// scope of the borrow.

fn main() {
    let mut a;
    loop {
        a = true;
        let b = &a;
        if a { break; }
        let c = &a;
    }
}

// END RUST SOURCE
// START rustc.node4.TypeckMir.before.mir
//     bb0: {
//         StorageLive(_1);
//         goto -> bb1;
//     }
//     bb1: {
//         _1 = const true;
//         StorageLive(_3);
//         _3 = &'21ce _1;
//         StorageLive(_5);
//         _5 = _1;
//         StorageDead(_5); // (see issue #38669)
//         if(_5) -> [true: bb2, false: bb3];
//     }
//     bb2: { // breaking out of loop ends the `let b = &a` borrow.
//         StorageDead(_3);
//         EndRegion('21ce);
//         StorageDead(_1);
//         return;
//     }
//     bb3: {
//         StorageLive(_8);
//         _8 = &'37ce _1;
//         StorageDead(_8);
//         EndRegion('37ce);
//         StorageDead(_3);
//         EndRegion('21ce);
//         goto -> bb1;
//     }
// END rustc.node4.TypeckMir.before.mir
