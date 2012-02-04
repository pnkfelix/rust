// Test various bindable expressions beyond mere calls.

type rec = { a: int, b: fn@(int, int) -> int };

impl rec for rec {
    fn c(x: int, y: int) -> int {
        self.a + x + y
    }
}

fn adder(x: int, y: int) -> int { x + y }

fn do_it(f: fn(rec) -> int) -> int {
    let rec = { a: 22, b: adder };
    f(rec)
}

fn main() {
    assert do_it(_.a) == 22;
    assert do_it(_.b(2, 3)) == 5;
    assert do_it(_.c(2, 3)) == 27;

    let rec: rec = { a: 22, b: adder };

    let rec_b = rec.b(_, _);
    assert rec_b(2, 3) == 5;

    let rec_c = rec.c(_, _);
    assert rec_c(2, 3) == 27;
}