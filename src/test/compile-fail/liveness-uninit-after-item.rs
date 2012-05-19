fn main() {
    let bar;
    fn baz(x: int) { }
    bind baz(bar); //! ERROR use of variable that may not have been initialized
}

