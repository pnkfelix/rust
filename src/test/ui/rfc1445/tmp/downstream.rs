#![feature(core_panic)]
#![no_std]
extern crate std;

struct Droppable;

impl Drop for Droppable {
    fn drop(&mut self) {
        let msg = "Dropping a Droppable\n";
        extern "C" { fn putchar(b: u8); }
        for c in msg.chars() {
            unsafe { putchar(c as u8); }
        }
    }
}

fn main() {
    let _guard = Droppable;
    core::panicking::panic(&("???", "downstream.rs", 17, 4))
}
