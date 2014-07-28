#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

pub struct Range<A> {
    state: A,
    stop: A,
    one: A
}

impl<T> Option<T> {
    fn map<A>(self, f: |T| -> A) -> Option<A> { loop { } }
}

trait ToNums {
    fn to_i64(&self) -> Option<i64> { loop { } }
    fn to_u64(&self) -> Option<u64> { loop { } }
    fn to_uint(&self) -> Option<uint> { loop { } }
}

trait CheckedSub {
    fn checked_sub(&self, y: &Self) -> Option<Self> { loop { } }
}
impl CheckedSub for i64 {}
impl CheckedSub for u64 {}
impl ToNums for i64 {}
impl ToNums for u64 {}

#[inline]
fn size_hint<A:ToNums>(_self: &Range<A>) -> (uint, Option<uint>) {
    // This first checks if the elements are representable as i64. If they aren't, try u64 (to
    // handle cases like range(huge, huger)). We don't use uint/int because the difference of
    // the i64/u64 might lie within their range.
    let bound = match _self.state.to_i64() {
        Some(a) => {
            let sz = _self.stop.to_i64().map(|b| b.checked_sub(&a));
            match sz {
                Some(Some(bound)) => bound.to_uint(),
                _ => None,
            }
        },
        None => match _self.state.to_u64() {
            Some(a) => {
                let sz = _self.stop.to_u64().map(|b| b.checked_sub(&a));
                match sz {
                    Some(Some(bound)) => bound.to_uint(),
                    _ => None
                }
            },
            None => None
        }
    };

    match bound {
        Some(b) => (b, Some(b)),
        // Standard fallback for unbounded/unrepresentable bounds
        None => (0, None)
    }
}
