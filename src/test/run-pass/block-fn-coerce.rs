fn force_add(f: fn() -> int, x: int) -> int { ret f() + x; }
fn main() {
    fn f() -> int { ret 7; }
    assert (force_add(f, 3) == 10);
    let g = force_add(f, _);
    assert (g(3) == 10);
}
