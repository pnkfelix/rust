fn wrapper3<T: copy>(i: T, j: int) {
    log(debug, i);
    log(debug, j);
    // This is a regression test that the spawn3 thunk to wrapper3
    // correctly finds the value of j
    assert j == 123456789;
}

fn spawn3<T: copy>(i: T, j: int) {
    wrapper3(_, j)(i);
    wrapper3(i, _)(j);
}

fn main() {
    spawn3(127u8, 123456789);
}