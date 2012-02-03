


// -*- rust -*-
fn add(n: int, m: int) -> int { ret n+m; }

fn main() {
    let g: fn@(int) -> int = add(10, _);
    let i: int = g(1);
    assert (i == 11);
}
