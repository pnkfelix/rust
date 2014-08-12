#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub trait Float {
    fn infinity() -> Self;
    fn neg_infinity() -> Self;
    fn foo(self) -> bool;
}

impl Float for f32 {
    #[inline]
    fn foo(self) -> bool {
        self == Float::infinity() || self == Float::neg_infinity()
    }
    fn infinity() -> f32 { loop { } }
    fn neg_infinity() -> f32 { loop { } }
}
