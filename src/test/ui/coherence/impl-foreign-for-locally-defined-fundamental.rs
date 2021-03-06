#![feature(fundamental)]
#![feature(re_rebalance_coherence)]

// compile-flags:--crate-name=test
// aux-build:coherence_lib.rs
// check-pass

extern crate coherence_lib as lib;
use lib::*;

#[fundamental]
struct Local;

impl Remote for Local {}

fn main() {}
