

fn id<T: copy>(t: T, x: int) -> T { ret t; }

fn main() {
    let t = {a: 1, b: 2, c: 3, d: 4, e: 5, f: 6, g: 7};
    assert (t.f == 6);
    let f0 = id(t, _); // introduce dummy param so I can use bind syntax
    assert (f0(0).f == 6);
}
