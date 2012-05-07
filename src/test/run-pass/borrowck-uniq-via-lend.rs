fn borrow(_v: &int) {}

fn local() {
    let mut v = ~3;
    borrow(v);
}

fn local_rec() {
    let mut v = {f: ~3};
    borrow(v.f);
}

fn local_recs() {
    let mut v = {f: {g: {h: ~3}}};
    borrow(v.f.g.h);
}

fn aliased_imm() { // NDM: Spurious
    let mut v = ~3;
    let w = &v; //! WARNING Illegal borrow: mutability mismatch, required immutable but found mutable
    borrow(v);
}

fn aliased_const() {
    let mut v = ~3;
    let w = &const v;
    borrow(v);
}

fn aliased_mut() {
    let mut v = ~3;
    let w = &mut v; //! NOTE Prior loan as mutable granted here
    borrow(v); //! WARNING Loan of mutable local variable as immutable conflicts with prior loan
}

fn aliased_other() {
    let mut v = ~3, w = ~4;
    let x = &mut w;
    borrow(v);
}

fn aliased_other_reassign() {
    let mut v = ~3, w = ~4;
    let mut x = &mut w;
    x = &mut v; //! NOTE Prior loan as mutable granted here
    borrow(v); //! WARNING Loan of mutable local variable as immutable conflicts with prior loan
}

fn main() {
}
