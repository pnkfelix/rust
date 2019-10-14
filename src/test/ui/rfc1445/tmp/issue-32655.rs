macro_rules! evil {
    () => {
        #[derive_Debug]
        struct Foo;
    }
}
evil!();
fn main() {}
