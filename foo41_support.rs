#![feature(lang_items)]
#![feature(macro_rules)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

#[macro_export]
macro_rules! debug_or(
    ($arg1:expr, $arg2:expr) => (if cfg!(not(ndebug)) { $arg1 } else { $arg2 })
)
