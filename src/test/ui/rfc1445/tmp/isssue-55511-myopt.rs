#![warn(indirect_structural_match)]
use std::cell::Cell;

#[derive(PartialEq, Eq)]
enum MyOption<T> {
    Some(T),
    None,
}
trait Foo<'a> {
    const C: MyOption<Cell<&'a u32>>;
}

impl<'a, T> Foo<'a> for T {
    const C: MyOption<Cell<&'a u32>> = MyOption::None;
}

fn main() {
    let a = 22;
    let b = MyOption::Some(Cell::new(&a));
    //~^ ERROR `a` does not live long enough [E0597]
    match b {
        <() as Foo<'static>>::C => { }
        //~^ WARN must be annotated with `#[derive(PartialEq, Eq)]`
        //~| WARN will become a hard error in a future release
        _ => { }
    }
}
