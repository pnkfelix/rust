// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::int;
use std::uint;

pub fn main() {
    println(fmt!("num-range start"));
    // int and uint have same result for
    //   Sum{2 <= i < 100} == (Sum{1 <= i <= 99} - 1) == n*(n+1)/2 - 1 for n=99
    let mut sum = 0u;
    for uint::range(2, 100) |i| { // Sum{2 <= i < 101}
        println(fmt!("num-range first i:%u", i));
        sum += i;
    }
    assert_eq!(sum, 4949);

    let mut sum = 0i;
    for int::range(2, 100) |i| {
        sum += i;
    }
    assert_eq!(sum, 4949);


    // elements are visited in correct order
    let primes = [2,3,5,7];
    let mut prod = 1i;
    for uint::range(0, 4) |i| {
        prod *= int::pow(primes[i], i);
    }
    assert_eq!(prod, 1*3*5*5*7*7*7);
    let mut prod = 1i;
    for int::range(0, 4) |i| {
        prod *= int::pow(primes[i], i as uint);
    }
    assert_eq!(prod, 1*3*5*5*7*7*7);


    // empty ranges
    for int::range(10, 10) |_| {
        fail!("range should be empty when start == stop");
    }

    for uint::range(10, 10) |_| {
        fail!("range should be empty when start == stop");
    }


    // range iterations do not wrap/overflow
    let mut oflo_loop_visited = ~[];
    for uint::range_step(uint::max_value-15, uint::max_value, 4) |x| {
        oflo_loop_visited.push(uint::max_value - x);
    }
    assert_eq!(oflo_loop_visited, ~[15, 11, 7, 3]);

    let mut oflo_loop_visited = ~[];
    for int::range_step(int::max_value-15, int::max_value, 4) |x| {
        oflo_loop_visited.push(int::max_value - x);
    }
    assert_eq!(oflo_loop_visited, ~[15, 11, 7, 3]);


    // range_step never passes nor visits the stop element
    for int::range_step(0, 21, 3) |x| {
        assert!(x < 21);
    }

    // range_step_inclusive will never pass stop element, and may skip it.
    let mut saw21 = false;
    for uint::range_step_inclusive(0, 21, 4) |x| {
        assert!(x <= 21);
        if x == 21 { saw21 = true; }
    }
    assert!(!saw21);
    let mut saw21 = false;
    for int::range_step_inclusive(0, 21, 4) |x| {
        assert!(x <= 21);
        if x == 21 { saw21 = true; }
    }
    assert!(!saw21);

    // range_step_inclusive will never pass stop element, but may visit it.
    let mut saw21 = false;
    for uint::range_step_inclusive(0, 21, 3) |x| {
        assert!(x <= 21);
        println(fmt!("saw: %u", x));
        if x == 21 { saw21 = true; }
    }
    assert!(saw21);
    let mut saw21 = false;
    for int::range_step_inclusive(0, 21, 3) |x| {
        assert!(x <= 21);
        if x == 21 { saw21 = true; }
    }
    assert!(saw21);

}
