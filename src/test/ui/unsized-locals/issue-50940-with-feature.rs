#![feature(unsized_fn_params)]
//~^ WARN the feature `unsized_fn_params` is incomplete and may cause the compiler to crash

fn main() {
    struct A<X: ?Sized>(X);
    A as fn(str) -> A<str>;
    //~^ERROR the size for values of type `str` cannot be known at compilation time
}
