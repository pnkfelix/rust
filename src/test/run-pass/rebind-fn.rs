fn add(i: int, j: int, k: int) -> int { ret i + j + k; }

fn binder(n: int) -> fn@(int) -> int {
    let f = add(n, _, _);
    ret f(2, _);
}
fn main() {
    binder(5);
    let f = binder(1);
    assert (f(1) == 4);
    assert (binder(8)(1) == 11);
}
