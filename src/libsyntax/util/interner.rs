// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// An "interner" is a data structure that associates values with uint tags and
// allows bidirectional lookup; i.e. given a value, one can easily find the
// type, and vice versa.

use std;
use std::hashmap::HashMap;
use std::hash::HashUtil;
use std::vec;
use std::str;
use std::ptr;

/// An interner that serves to store strings with as little overhead as possible
pub struct Interner {
    /// This is a weird little "multi hashmap" that holds together on the
    /// basis of knowing that it will never shrink. We map from the
    /// hash-of-a-string to the offset in buf. If the string found at
    /// that offset is not the value we want, we increment the hash and
    /// try again.
    map: HashMap<u64, uint>,
              
    /// Buf is a concatenation of all strings, with nulls between
    /// them. We assume that storing a null is smaller than a len in
    /// each key.
    buf: ~[u8]
}
 
impl Interner {
    priv fn str_at<'a>(&'a self, off: uint) -> &'a str {
        let mut len = 0;
        while self.buf[off + len] != 0 {
            len += 1;
        }
        let slice = self.buf.slice(off, off + len + 1);
        str::from_bytes_with_null(slice)
    }

    #[inline]
    priv fn store_inside(&mut self, val: &str) -> uint {
        let tag = self.buf.len();
        vec::reserve(&mut self.buf, tag + val.len());
        unsafe {
            let valbuf: &mut [u8] = std::cast::transmute(val);
            let bufptr: *u8 = vec::raw::to_ptr(self.buf);
            std::ptr::copy_nonoverlapping_memory(ptr::offset(bufptr, tag) as *mut u8,
                                                 vec::raw::to_mut_ptr(valbuf), val.len());
            vec::raw::set_len(&mut self.buf, tag + val.len());
        }
        self.buf.push(0);
        return tag
    }

    pub fn new() -> Interner {
        Interner {
            map: HashMap::new(),
            buf: ~[]
        }
    }

    pub fn intern(&mut self, val: &str) -> uint {
        match self.find(val) {
            Some(tag) => tag,
            None => {
                let tag = self.store_inside(val);
                self.map.insert(val.hash(), tag);
                tag
            }
        }
    }

    pub fn prefill(val: &[&str]) -> Interner {
        let mut in = Interner::new();
        for val.iter().advance |x| {
            in.intern(*x);
        }
        in
    }
    
    pub fn gensym(&mut self, val: &str) -> uint {
        self.store_inside(val)
    }
     
    pub fn find(&self, val: &str) -> Option<uint> {
        let mut hash = val.hash();
        loop {
            match self.map.find(&hash) {
                Some(v) => {
                    let s = self.str_at(*v);
                    if s == val {
                        return Some(*v);
                    } else {
                        hash += 1;
                    }
                }
                None => return None
            }
        }
    }

    pub fn get<'a>(&'a self, tag: uint) -> Option<&'a str> {
        if tag <= self.buf.len() {
            Some(self.str_at(tag))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i1 () {
        let i = Interner::new();
        assert!(i.get(13).is_none());
    }

    #[test]
    fn i2 () {
        let mut i = Interner::new();
        // first one is zero:
        assert_eq!(i.intern ("dog"), 0);
        // re-use gets the same entry:
        assert_eq!(i.intern ("dog"), 0);
        // different string gets a different #:
        assert_eq!(i.intern ("cat"), 4);
        assert_eq!(i.intern ("cat"), 4);
        // dog is still at zero
        assert_eq!(i.intern ("dog"), 0);
        // gensym gets 3
        assert_eq!(i.gensym ("zebra" ), 8);
        // gensym of same string gets new number :
        assert_eq!(i.gensym ("zebra" ), 14);
        // gensym of *existing* string gets new number:
        assert_eq!(i.gensym ("dog"), 20);
        assert!(i.get(0).unwrap() == "dog");
        assert!(i.get(4).unwrap() == "cat");
        assert!(i.get(8).unwrap() == "zebra");
        assert!(i.get(14).unwrap() == "zebra");
        assert!(i.get(20).unwrap() == "dog");
    }

    #[test]
    fn i3 () {
        let mut i = Interner::prefill(&["Alan","Bob","Carol"]);
        assert!(i.get(0).unwrap() == "Alan");
        assert!(i.get(5).unwrap() == "Bob");
        assert!(i.get(9).unwrap() == "Carol");
        assert_eq!(i.intern("Bob"), 5);
    }
}
