// compile-flags: -Cno-prepopulate-passes

// revisions:x86_64 i686 aarch64-apple aarch64-windows aarch64-linux arm riscv
// needs-llvm-components: aarch64 arm riscv

//[x86_64] compile-flags: --target x86_64-unknown-uefi
//[i686] compile-flags: --target i686-unknown-linux-musl
//[aarch64-windows] compile-flags: --target aarch64-unknown-none
//[aarch64-linux] compile-flags: --target aarch64-unknown-none
//[aarch64-apple] compile-flags: --target aarch64-apple-darwin
//[arm] compile-flags: --target armv7r-none-eabi
//[riscv] compile-flags: --target riscv64gc-unknown-none-elf

// See bottom of file for a corresponding C source file that is meant to yield
// equivalent declarations.
#![feature(no_core, lang_items)]
#![crate_type = "lib"]
#![no_std]
#![no_core]

#[lang="sized"] trait Sized { }
#[lang="freeze"] trait Freeze { }
#[lang="copy"] trait Copy { }

// CHECK: void @c_arg_u8(i8 zeroext %_a)
#[no_mangle] pub extern "C" fn c_arg_u8(_a: u8) { }
// CHECK: void @c_arg_u16(i16 zeroext %_a)
#[no_mangle] pub extern "C" fn c_arg_u16(_a: u16) { }
// CHECK: void @c_arg_u32(i32 %_a)
#[no_mangle] pub extern "C" fn c_arg_u32(_a: u32) { }
// CHECK: void @c_arg_u64(i64 %_a)
#[no_mangle] pub extern "C" fn c_arg_u64(_a: u64) { }

// CHECK: void @c_arg_i8(i8 signext %_a)
#[no_mangle] pub extern "C" fn c_arg_i8(_a: i8) { }
// CHECK: void @c_arg_i16(i16 signext %_a)
#[no_mangle] pub extern "C" fn c_arg_i16(_a: i16) { }
// CHECK: void @c_arg_i32(i32 %_a)
#[no_mangle] pub extern "C" fn c_arg_i32(_a: i32) { }
// CHECK: void @c_arg_i64(i64 %_a)
#[no_mangle] pub extern "C" fn c_arg_i64(_a: i64) { }

// CHECK: zeroext i8 @c_ret_u8()
#[no_mangle] pub extern "C" fn c_ret_u8() -> u8 { 0 }
// CHECK: zeroext i16 @c_ret_u16()
#[no_mangle] pub extern "C" fn c_ret_u16() -> u16 { 0 }
// CHECK: i32 @c_ret_u32()
#[no_mangle] pub extern "C" fn c_ret_u32() -> u32 { 0 }
// CHECK: i64 @c_ret_u64()
#[no_mangle] pub extern "C" fn c_ret_u64() -> u64 { 0 }

// CHECK: signext i8 @c_ret_i8()
#[no_mangle] pub extern "C" fn c_ret_i8() -> i8 { 0 }
// CHECK: signext i16 @c_ret_i16()
#[no_mangle] pub extern "C" fn c_ret_i16() -> i16 { 0 }
// CHECK: i32 @c_ret_i32()
#[no_mangle] pub extern "C" fn c_ret_i32() -> i32 { 0 }
// CHECK: i64 @c_ret_i64()
#[no_mangle] pub extern "C" fn c_ret_i64() -> i64 { 0 }

const C_SOURCE_FILE: &'static str = r##"
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

void c_arg_u8(uint8_t _a) { }
void c_arg_u16(uint16_t _a) { }
void c_arg_u32(uint32_t _a) { }
void c_arg_u64(uint64_t _a) { }

void c_arg_i8(int8_t _a) { }
void c_arg_i16(int16_t _a) { }
void c_arg_i32(int32_t _a) { }
void c_arg_i64(int64_t _a) { }

uint8_t  c_ret_u8()  { return 0; }
uint16_t c_ret_u16() { return 0; }
uint32_t c_ret_u32() { return 0; }
uint64_t c_ret_u64() { return 0; }

int8_t   c_ret_i8()  { return 0; }
int16_t  c_ret_i16() { return 0; }
int32_t  c_ret_i32() { return 0; }
int64_t  c_ret_i64() { return 0; }
"##;
