fn f(i: int) {
}

fn main() {
    // Can't produce a bare function by binding
    let g: native fn(int) = f(_);
    //!^ ERROR expected `native fn(int)` but found `fn@(int)`
    //!^^ ERROR expected `native fn(int)` but found `fn@(
    // ... For some reason, we get two error msgs here, one of which
    // ... mentions the raw variables.  I think this comes about
    // ... because we first unify with the expected type and then unify
    // ... another time.
}
