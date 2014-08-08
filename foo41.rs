#![feature(lang_items)]
#![feature(macro_rules)]
#![feature(phase)]
#![no_std]
#![crate_type="lib"]

#[phase(plugin)]
extern crate foo41_support;

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }


pub fn foo() {
    let a1 = box 3i;
    let a2 = box 4i;
    let b = debug_or!(proc(x:int)x+*a1,proc(y:int)y+*a2);
    let _c = b(1);
}

pub fn main() { foo() }
