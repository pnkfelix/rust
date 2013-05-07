// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// allow the ice_fail macro to escape this module:
#[macro_escape];

//condition! {
//    // FIXME (#6009): uncomment `pub` after expansion support lands.
//    /*pub*/ ice: ~str -> ();
//}
            pub mod ice {
                fn key(_x: @::core::condition::Handler<~str,()>) { }

                pub static cond :
                    ::core::condition::Condition<'static,~str,()> =
                    ::core::condition::Condition {
                        name: stringify!(ice),
                        key: key
                    };
            }

macro_rules! ice_fail(
        () => ( ice_fail!(~"explicit failure") );
        ($msg:expr) => ( { ice::cond.raise($msg); fail!($msg); } )
)
