// #![no_std]
#![feature(asm)]

// fn foo(x: int) { println!("{}", x); }
fn foo(_x: int) { /*println!("{}", x);*/ }

pub fn main() {
    let x: int;
    unsafe {
        asm!("mov $1, $0" : "=r"(x) : "r"(x)); //~ ERROR use of possibly uninitialized variable: `x`
    }
    foo(x);
}
