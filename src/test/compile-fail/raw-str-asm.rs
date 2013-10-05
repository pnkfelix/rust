// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// The input/output/clobbers/option string options in the inline asm syntax
// extension don't currently store whether they were a raw string literal in
// the ast, so the pretty printer wouldn't be able to reproduce them
// precisely if they were. So we don't allow that for now.

// example from PR 5359
fn addsub(a: int, b: int) -> (int, int) {
    let mut c = 0;
    let mut d = 0;
    unsafe {
        asm!(r"add $4, $0
               sub $4, $1"
             : r"=r"(c), r"=r"(d)
             //~^ ERROR asm output can't be raw string
             //~^^ ERROR asm output can't be raw string
             : r"0"(a), r"1"(a), r"r"(b)
             //~^ ERROR asm input can't be raw string
             //~^^ ERROR asm input can't be raw string
             //~^^^ ERROR asm input can't be raw string
             );
    }
    (c, d)
}

fn main() {
}
