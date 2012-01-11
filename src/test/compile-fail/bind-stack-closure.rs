// -*- rust -*-

fn foo(x: block()) {
    bind x(); //! ERROR cannot bind block closures
}

fn main() {
}
