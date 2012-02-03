

fn foo(a: @int, b: @int) -> int { ret *a + *b; }

fn main() {
    let f1 = fn@() -> int { foo(@10, @12) };
    assert (f1() == 22);
}
