#![crate_type="lib"]
#![no_std]

// #[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum MyOption<T> {
    None,
    Some(T),
}

impl<T> MyOption<T> {
    #[inline]
    pub fn expect(self, s: &str) -> T {
        match self {
            MyOption::Some(t) => return t,
            MyOption::None => expect_failed(s),
        }
    }
}

#[inline(never)]
#[cold]
fn expect_failed(msg: &str) -> ! {
    panic!("{}", msg)
}
