// error-pattern: mismatched types: expected () but found int
// error-pattern: binary operation + cannot be applied to type `()`
fn main() {
    let x = if true { 3 };
    log x + 5;
}
