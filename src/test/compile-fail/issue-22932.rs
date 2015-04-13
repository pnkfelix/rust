// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Issue 22932: `panic!("{}");` should not compile.

pub fn f1() { panic!("this does not work {}");
              //~^ ERROR panic! input cannot be format string literal
}

pub fn workaround_1() {
    panic!(("This *does* works {}"));
}

pub fn workaround_2() {
    const MSG: &'static str = "This *does* work {}";
    panic!(MSG);
}

pub fn f2() { panic!("this does not work {");
              //~^ ERROR panic! input cannot be format string literal
}

pub fn f3() { panic!("nor this }");
              //~^ ERROR panic! input cannot be format string literal
}

pub fn f4() { panic!("nor this {{");
              //~^ ERROR panic! input cannot be format string literal
}

pub fn f5() { panic!("nor this }}");
              //~^ ERROR panic! input cannot be format string literal
}

pub fn f0_a() {
    ensure_not_fmt_string_literal!("`f0_a`", "this does not work {}");
    //~^ ERROR `f0_a` input cannot be format string literal
}

pub fn f0_b() {
    println!(ensure_not_fmt_string_literal!("`f0_b`", "this does work"));
}

pub fn main() {}
