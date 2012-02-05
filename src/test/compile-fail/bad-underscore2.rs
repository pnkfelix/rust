fn one(f: fn(int)) {}
fn two(f: fn(int, int)) {}

fn main() {
    two(_ + _); //! ERROR `_` can only appear as part of
}