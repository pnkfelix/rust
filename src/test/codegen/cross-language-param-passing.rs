#![crate_type = "lib"]

#[no_mangle] pub extern "C" fn c_pass_u8_to_rust(a: u8, f: extern "Rust" fn (u8)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_u16_to_rust(a: u16, f: extern "Rust" fn (u16)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_u32_to_rust(a: u32, f: extern "Rust" fn (u32)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_u64_to_rust(a: u64, f: extern "Rust" fn (u64)) { f(a); }

#[no_mangle] pub extern "C" fn c_pass_i8_to_rust(a: i8, f: extern "Rust" fn (i8)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_i16_to_rust(a: i16, f: extern "Rust" fn (i16)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_i32_to_rust(a: i32, f: extern "Rust" fn (i32)) { f(a); }
#[no_mangle] pub extern "C" fn c_pass_i64_to_rust(a: i64, f: extern "Rust" fn (i64)) { f(a); }

#[no_mangle] pub extern "Rust" fn rust_pass_u8_to_c(a: u8, f: extern "C" fn (u8)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_u16_to_c(a: u16, f: extern "C" fn (u16)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_u32_to_c(a: u32, f: extern "C" fn (u32)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_u64_to_c(a: u64, f: extern "C" fn (u64)) { f(a); }

#[no_mangle] pub extern "Rust" fn rust_pass_i8_to_c(a: i8, f: extern "C" fn (i8)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_i16_to_c(a: i16, f: extern "C" fn (i16)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_i32_to_c(a: i32, f: extern "C" fn (i32)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_pass_i64_to_c(a: i64, f: extern "C" fn (i64)) { f(a); }

#[no_mangle] pub extern "C" fn c_ret_u8_from_rust(a: u8, f: extern "Rust" fn (u8)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_u16_from_rust(a: u16, f: extern "Rust" fn (u16)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_u32_from_rust(a: u32, f: extern "Rust" fn (u32)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_u64_from_rust(a: u64, f: extern "Rust" fn (u64)) { f(a); }

#[no_mangle] pub extern "C" fn c_ret_i8_from_rust(a: i8, f: extern "Rust" fn (i8)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_i16_from_rust(a: i16, f: extern "Rust" fn (i16)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_i32_from_rust(a: i32, f: extern "Rust" fn (i32)) { f(a); }
#[no_mangle] pub extern "C" fn c_ret_i64_from_rust(a: i64, f: extern "Rust" fn (i64)) { f(a); }

#[no_mangle] pub extern "Rust" fn rust_ret_u8_from_c(a: u8, f: extern "C" fn (u8)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_u16_from_c(a: u16, f: extern "C" fn (u16)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_u32_from_c(a: u32, f: extern "C" fn (u32)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_u64_from_c(a: u64, f: extern "C" fn (u64)) { f(a); }

#[no_mangle] pub extern "Rust" fn rust_ret_i8_from_c(a: i8, f: extern "C" fn (i8)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_i16_from_c(a: i16, f: extern "C" fn (i16)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_i32_from_c(a: i32, f: extern "C" fn (i32)) { f(a); }
#[no_mangle] pub extern "Rust" fn rust_ret_i64_from_c(a: i64, f: extern "C" fn (i64)) { f(a); }
