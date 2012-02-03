enum chan { chan_t, }

fn wrapper3(i: chan) {
    assert i == chan_t;
}

fn main() {
    let wrapped = fn@() { wrapper3(chan_t) };
    wrapped();
}
