// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Exposes the NonZero lang item which provides optimization hints.
#![unstable(feature = "nonzero",
            reason = "needs an RFC to flesh out the design",
            issue = "27730")]

use marker::Sized;
use ops::{CoerceUnsized, Deref};

/// Unsafe trait to indicate what types are usable with the NonZero struct
pub unsafe trait Zeroable {
    /// Returns true if and only if `*self` is a zero value.
    fn is_zero(&self) -> bool;
}

unsafe impl<T:?Sized> Zeroable for *const T {
    fn is_zero(&self) -> bool { (*self as *const u8).is_null() }
}
unsafe impl<T:?Sized> Zeroable for *mut T {
    fn is_zero(&self) -> bool { (*self as *mut u8).is_null() }
}
unsafe impl Zeroable for isize { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for usize { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for i8 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for u8 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for i16 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for u16 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for i32 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for u32 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for i64 { fn is_zero(&self) -> bool { *self == 0 } }
unsafe impl Zeroable for u64 { fn is_zero(&self) -> bool { *self == 0 } }

/// A wrapper type for raw pointers and integers that will never be
/// NULL or 0 that might allow certain optimizations.
#[lang = "non_zero"]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct NonZero<T: Zeroable>(T);

impl<T: Zeroable> NonZero<T> {
    /// Creates an instance of NonZero with the provided value.
    /// You must indeed ensure that the value is actually "non-zero".
    #[inline(always)]
    pub unsafe fn new(inner: T) -> NonZero<T> {
        debug_assert!(!inner.is_zero());
        NonZero(inner)
    }
}

impl<T: Zeroable> Deref for NonZero<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        let NonZero(ref inner) = *self;
        inner
    }
}

impl<T: Zeroable+CoerceUnsized<U>, U: Zeroable> CoerceUnsized<NonZero<U>> for NonZero<T> {}
