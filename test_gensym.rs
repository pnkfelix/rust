// test_gensym.rs

// Taken from Issue #15962

#![feature(phase)]

#[phase(plugin)] extern crate gensym;

fn main() {
    let a = test_quote!();
}
