enum foo = ~uint;

impl foo: add<foo, foo> {
    pure fn add(f: foo) -> foo {
        foo(~(**self + **f))
    }
}

fn main() {
    let x = foo(~3);
    let y = x + move x;
    //~^ ERROR moving out of immutable local variable prohibited due to outstanding loan
}
