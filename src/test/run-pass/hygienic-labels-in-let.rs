// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ignore-pretty: pprust doesn't print hygiene output

#![allow(unreachable_code)]

macro_rules! loop_x {
    ($e: expr) => {
        // $e shouldn't be able to interact with this 'x
        'x: loop { $e }
    }
}

macro_rules! while_true {
    ($e: expr) => {
        // $e shouldn't be able to interact with this 'x
        'x: while 1 + 1 == 2 { $e }
    }
}

macro_rules! run_once {
    ($e: expr) => {
        // ditto
        'x: for _ in 0..1 { $e }
    }
}

pub fn main() {
    f1();
    f2();
    f3();
    f4();
}

fn f1() {
    let i = 0;
    let j: isize = {
        'x: loop {
            // this 'x should refer to the outer loop, lexically
            loop_x!(break 'x);
            panic!("break doesn't act hygienically inside loop in let");
        }
        i + 1
    };
    assert_eq!(j, 1);
}

fn f2() {
    let i = 0;
    let k: isize = {
        'x: for _ in 0..1 {
            // ditto
            loop_x!(break 'x);
            panic!("break doesn't act hygienically inside for loop in let");
        }
        i + 1
    };
    assert_eq!(k, 1);
}

fn f3() {
    let i = 0;
    let l: isize = {
        'x: for _ in 0..1 {
            // ditto
            while_true!(break 'x);
            panic!("break doesn't act hygienically inside for loop in let");
        }
        i + 1
    };
    assert_eq!(l, 1);
}

fn f4() {
    let i = 0;
    let n: isize = {
        'x: for _ in 0..1 {
            // ditto
            run_once!(continue 'x);
            panic!("break doesn't act hygienically inside for loop in let");
        }
        i + 1
    };
    assert_eq!(n, 1);
}
