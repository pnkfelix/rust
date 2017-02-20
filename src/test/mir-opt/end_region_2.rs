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

// We will EndRegion for borrows in a loop that occur before break but
// not those after break.

fn main() {
    loop {
        let a = true;
        let b = &a;
        if a { break; }
        let c = &a;
    }
}

// END RUST SOURCE
// START rustc.node4.TypeckMir.before.mir
//     bb1: {
//         StorageLive(_2);
//         _2 = const true;
//         StorageLive(_3);
//         _3 = &'17ce _2;
//         StorageLive(_5);
//         _5 = _2;
//         StorageDead(_5); // (see issue #38669)
//         if(_5) -> [true: bb2, false: bb3];
//     }
//     bb2: {
//         StorageDead(_3);
//         EndRegion('17ce);
//         StorageDead(_2);
//         return;
//     }
//     bb3: {
//         StorageLive(_8);
//         _8 = &'33ce _2;
//         StorageDead(_8);
//         EndRegion('33ce);
//         StorageDead(_3);
//         EndRegion('17ce);
//         StorageDead(_2);
//         goto -> bb1;
//     }
// END rustc.node4.TypeckMir.before.mir
