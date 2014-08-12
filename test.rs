#![feature(phase)]

// Taken from Issue #15750

#[phase(plugin)]
extern crate plugin;

fn main() {
    let x = 3i;
    println!("{}", mymacro!(x));
}
