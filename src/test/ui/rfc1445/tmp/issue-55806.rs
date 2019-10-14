#[stable(feature = "unit_test", since="1.0.0")]
#![feature(const_fn, staged_api, rustc_attrs)]

#[stable(feature = "unit_test", since="1.0.0")]
#[rustc_promotable]
const fn bar() -> u8 { 10 }

fn main() {
    let _x: &'static _ = &bar();
}
