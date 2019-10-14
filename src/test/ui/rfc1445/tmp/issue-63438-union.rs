struct S {
    s1: i32,
}

enum E {
    E1(i32),
    E2(i32),
}

const SS: &S = &S { s1: 0 };
const EE: &E = &E::E1(0);

fn main() {
    match &(S { s1: 1 }) {
        SS => "hello",
        _ => "goodbye",
    };

    match &E::E2(1) {
        EE => "hello",
        _ => "goodbye",
    };
}
