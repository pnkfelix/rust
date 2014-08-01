#![feature(phase)]

// Taken from Issue #15750

#[phase(plugin)]
extern crate plugin;

fn main() {
    let x = 3;
    println!("{}", mymacro!(x));
}
