// #![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

// extracted version of ICE I encountered while bootstrapping libstd

extern crate core;
extern crate libc;
extern crate rustrt;
extern crate collections;

use rustrt::c_str::{CString, ToCStr};
use core::option::Option;
use core::ptr;
use core::result::{Result,Ok,Err};
use collections::string::String;

pub fn check_for_errors_in<T>(f: || -> T) -> Result<T, String> {
    use rustrt::mutex::{StaticNativeMutex, NATIVE_MUTEX_INIT};
    static mut lock: StaticNativeMutex = NATIVE_MUTEX_INIT;
    unsafe {
        // dlerror isn't thread safe, so we need to lock around this entire
        // sequence
        let _guard = lock.lock();
        let _old_error = dlerror();

        let result = f();

        let last_error = dlerror() as *const _;
        let ret = if ptr::null() == last_error {
            Ok(result)
            } else {
            Err(String::from_str(CString::new(last_error, false).as_str()
                                 .unwrap()))
        };

        ret
    }
}

fn dlerror() -> *mut libc::c_char { loop { } }
