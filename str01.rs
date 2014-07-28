#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

impl<T> Option<T> {
    fn map<A>(self, f: |T| -> A) -> Option<A> { loop { } }
}

mod slice {
    mod marker {
        #[lang="contravariant_lifetime"]
        pub struct ContravariantLifetime<'a>;
    }

    pub struct Items<'a, T> {
        ptr: *const T,
        end: *const T,
        marker: marker::ContravariantLifetime<'a>
    }
}

pub struct Chars<'a> {
    iter: slice::Items<'a, u8>
}

pub struct Utf16CodeUnits<'a> {
    chars: Chars<'a>,
    extra: u16
}

impl<'a> Chars<'a> {
    fn next(&mut self) -> Option<char> { loop { } }
}

trait EncodeUtf16 {
    fn encode_utf16(&self, buf: &mut [u16]) -> uint { loop { } }
}

impl EncodeUtf16 for char { }

impl<'a> Utf16CodeUnits<'a> {
    fn foo(&mut self) -> Option<u16> {
        if self.extra != 0 {
            let tmp = self.extra;
            self.extra = 0;
            return Some(tmp);
        }

        let mut buf = [0u16, ..2];
        self.chars.next().map(|ch| {
            let n = ch.encode_utf16(buf /* as mut slice! */);
            if n == 2 { self.extra = buf[1]; }
            buf[0]
        })
    }
}
