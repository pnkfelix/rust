// Test binding of arguments that have mode ++ where mode && is expected.
// (Inference should accomodate this)

fn adder(x: int, y: int) -> int { x + y }

fn main() {
    assert vec::foldl(0, [1, 2, 3], adder(_, _)) == 6;
    assert vec::map([1, 2, 3], adder(1, _)) == [2, 3, 4];
}