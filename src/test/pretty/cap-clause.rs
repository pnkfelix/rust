// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// pp-exact

fn main() {
    let x = 1;
    let y = 2;
    let z = 3;
    let l1: fn@(int) -> int = |w, copy x| { w + x + y };
    let l2: fn@(int) -> int = |w, copy x, move y| { w + x + y };
    let l3: fn@(int) -> int = |w, move z| { w + z };

    let x = 1;
    let y = 2;
    let z = 3;
    let s1: fn~(copy x) -> int = |copy x| { x + y };
    let s2: fn~(copy x, move y) -> int = |copy x, move y| { x + y };
    let s3: fn~(move z) -> int = |move z| { z };
}
