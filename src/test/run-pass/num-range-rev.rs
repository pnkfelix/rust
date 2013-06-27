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
    println(fmt!("num-range-rev start"));

    // int and uint have same result for
    //   Sum{100 > i >= 2} == (Sum{1 <= i <= 99} - 1) == n*(n+1)/2 - 1 for n=99
    let mut sum = 0u;
    for uint::range_rev(100, 2) |i| { // Sum(101 > i >= 2)
        // println(fmt!("num-range-rev first i:%u", i));
        sum += i;
    }
    assert_eq!(sum, 4949);

    let mut sum = 0i;
    for int::range_rev(100, 2) |i| {
        sum += i;
    }
    assert_eq!(sum, 4949);


    // elements are visited in correct order
    let primes = [2,3,5,7];
    let mut prod = 1i;
    for uint::range_rev(4, 0) |i| {
        prod *= int::pow(primes[i], i);
    }
    assert_eq!(prod, 2*2*2*3*3*5*1);
    let mut prod = 1i;
    for int::range_rev(4, 0) |i| {
        prod *= int::pow(primes[i], i as uint);
    }
    assert_eq!(prod, 2*2*2*3*3*5*1);


    // range and range_rev are symmetric.
    let mut sum_up = 0u;
    for uint::range(10, 30) |i| {
        sum_up += i;
    }
    let mut sum_down = 0u;
    for uint::range_rev(30, 10) |i| {
        sum_down += i;
    }
    assert_eq!(sum_up, sum_down);

    let mut sum_up = 0;
    for int::range(-20, 10) |i| {
        sum_up += i;
    }
    let mut sum_down = 0;
    for int::range_rev(10, -20) |i| {
        sum_down += i;
    }
    assert_eq!(sum_up, sum_down);


    // empty ranges
    for int::range_rev(10, 10) |_| {
        fail!("range should be empty when start == stop");
    }

    for uint::range_rev(0, 1) |_| {
        fail!("range should be empty when start-1 underflows");
    }

    // range iterations do not wrap/underflow
    let mut uflo_loop_visited = ~[];
    for int::range_step(int::min_value+15, int::min_value, -4) |x| {
        uflo_loop_visited.push(x - int::min_value);
    }
    assert_eq!(uflo_loop_visited, ~[15, 11, 7, 3]);

    let mut uflo_loop_visited = ~[];
    for uint::range_step(uint::min_value+15, uint::min_value, -4) |x| {
        uflo_loop_visited.push(x - uint::min_value);
    }
    assert_eq!(uflo_loop_visited, ~[15, 11, 7, 3]);
}
