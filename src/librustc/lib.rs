// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

The Rust compiler.

# Note

This API is completely unstable and subject to change.

*/

#![crate_name = "rustc"]
#![experimental]
#![comment = "The Rust compiler"]
#![license = "MIT/ASL2"]
#![crate_type = "dylib"]
#![crate_type = "rlib"]
#![doc(html_logo_url = "http://www.rust-lang.org/logos/rust-logo-128x128-blk-v2.png",
      html_favicon_url = "http://www.rust-lang.org/favicon.ico",
      html_root_url = "http://doc.rust-lang.org/master/")]

#![allow(deprecated)]
#![feature(macro_rules, globs, struct_variant, managed_boxes, quote)]
#![feature(default_type_params, phase, unsafe_destructor)]

#![allow(unknown_features)] // NOTE: Remove after next snapshot
#![feature(rustc_diagnostic_macros)]

extern crate alloc;
extern crate arena;
extern crate debug;
extern crate flate;
extern crate getopts;
extern crate graphviz;
extern crate libc;
extern crate llvm = "rustc_llvm";
extern crate rustc_back = "rustc_back";
extern crate serialize;
extern crate rbml;
extern crate time;
#[phase(plugin, link)] extern crate log;
#[phase(plugin, link)] extern crate syntax;

#[cfg(test)]
extern crate test;

mod diagnostics;

pub mod back {
    pub use rustc_back::abi;
    pub use rustc_back::archive;
    pub use rustc_back::arm;
    pub use rustc_back::mips;
    pub use rustc_back::mipsel;
    pub use rustc_back::rpath;
    pub use rustc_back::svh;
    pub use rustc_back::target_strs;
    pub use rustc_back::x86;
    pub use rustc_back::x86_64;

    pub mod link;
    pub mod lto;

}

pub mod middle {
    pub mod astencode;
    pub mod borrowck;
    pub mod cfg;
    pub mod check_const;
    pub mod check_loop;
    pub mod check_match;
    pub mod check_static;
    pub mod const_eval;
    pub mod dataflow;
    pub mod dead;
    pub mod def;
    pub mod dependency_format;
    pub mod effect;
    pub mod entry;
    pub mod expr_use_visitor;
    pub mod freevars;
    pub mod graph;
    pub mod intrinsicck;
    pub mod kind;
    pub mod lang_items;
    pub mod liveness;
    pub mod mem_categorization;
    pub mod pat_util;
    pub mod privacy;
    pub mod reachable;
    pub mod region;
    pub mod resolve;
    pub mod resolve_lifetime;
    pub mod save;
    pub mod stability;
    pub mod subst;
    pub mod trans;
    pub mod ty;
    pub mod ty_fold;
    pub mod typeck;
    pub mod weak_lang_items;
}

pub mod front {
    pub mod config;
    pub mod test;
    pub mod std_inject;
    pub mod assign_node_ids_and_map;
    pub mod feature_gate;
    pub mod show_span;
}

pub mod metadata;

pub mod driver;

pub mod plugin;

pub mod lint;

pub mod util {
    pub use rustc_back::fs;
    pub use rustc_back::sha2;

    pub mod common;
    pub mod ppaux;
    pub mod nodemap;
}

pub mod lib {
    pub use llvm;
}

__build_diagnostic_array!(DIAGNOSTICS)

// A private module so that macro-expanded idents like
// `::rustc::lint::Lint` will also work in `rustc` itself.
//
// `libstd` uses the same trick.
#[doc(hidden)]
mod rustc {
    pub use lint;
}

pub fn main() {
    use alloc::heap::imp::loud_heap;
    static mut delay: uint = 0u;
    fn report(m: loud_heap::Msg) {
        unsafe {
            if delay > 0 {
                delay -= 1;
                return;
            }
        }

        match m {
            loud_heap::As(s) => {
                println!("Allocate(size={:u}, align={:u})",
                         s.size, s.align);
            }
            loud_heap::Af(s) => {
                println!("Allocate(size={:u}, align={:u}) ret=0x{:010x}",
                         s.size, s.align, s.ret as uint);
            }
            loud_heap::Rs(s) => {
                println!("Reallocate(ptr=0x{:010x}, size={:u}, align={:u}, old_size={:u})",
                         s.ptr as uint, s.size, s.align, s.old_size);
            }
            loud_heap::Rf(s) => {
                println!("Reallocate(ptr=0x{:010x}, size={:u}, align={:u}, old_size={:u}) ret=0x{:010x}",
                         s.ptr as uint, s.size, s.align, s.old_size, s.ret as uint);
            }
            loud_heap::RIPs(s) => {
                println!("ReallocateInPlace(ptr=0x{:010x}, size={:u}, align={:u}, old_size={:u})",
                         s.ptr as uint, s.size, s.align, s.old_size);
            }
            loud_heap::RIPf(s) => {
                println!("ReallocateInPlace(ptr=0x{:010x}, size={:u}, align={:u}, old_size={:u}) ret={}",
                         s.ptr as uint, s.size, s.align, s.old_size, s.ret);
            }
            loud_heap::D(s) => {
                println!("Deallocate(ptr=0x{:010x}, size={:u}, align={:u})",
                         s.ptr as uint, s.size, s.align);
            }
        }
    }
    let d : Option<uint> = std::os::getenv("CFG_COMPILER_ALLOC_MSG_DELAY")
        .and_then(|x|from_str::<uint>(x.as_slice()));
    match d {
        None => {},
        Some(d) => {
            println!("registering loud_heap messenger with delay {}", d);
            unsafe { delay = d; }
            loud_heap::register_messenger(report)
        }
    }
    let args = std::os::args();
    std::os::set_exit_status(driver::main_args(args.as_slice()));
}
