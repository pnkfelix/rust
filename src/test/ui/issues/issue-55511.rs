#![warn(indirect_structural_match)]
use std::cell::Cell;
trait Foo<'a> {
    const C: Option<Cell<&'a u32>>;
}

impl<'a, T> Foo<'a> for T {
    const C: Option<Cell<&'a u32>> = None;
}

fn main() {
    let a = 22;
    let b = Some(Cell::new(&a));
    //~^ ERROR `a` does not live long enough [E0597]
    match b {
        // Below line used to cause structural match check to fire, before
        // rust-lang/rust#62614 was addressed.
        <() as Foo<'static>>::C => { }
        _ => { }
    }
}
