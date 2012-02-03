// error-pattern:fail

fn f(a: @int) {
    fail;
}

fn main() {
    let g = fn@() { f(@0) };
    g();
}