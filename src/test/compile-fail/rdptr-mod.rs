// error-pattern:foo

type T = {
    mutable f: uint
};

fn set_f(t: rd @T) {
    t.f = 22u;
}

fn main() {
}