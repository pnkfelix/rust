fn force(f: fn()) { f(); }
fn main() {
    let x: int;
    force(fn&() {
        log(debug, x); //! ERROR capture of variable that may not have been initialized
    });
}
