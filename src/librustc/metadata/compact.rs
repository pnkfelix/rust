// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// A very minimal encoder that tries to emit the minimum bytes that it
// can.  This is used for metadata encoding.

use core::io::{Writer, WriterUtil, Reader, ReaderUtil};
use core::io;
use core::str;
use core::vec;
use std::ebml;
use std::serialize::{Encoder, Decoder, Encodable, Decodable};

pub fn encode<S:Encodable<CompactEncoder>>(wr: @io::Writer, s: &S) {
    let enc = CompactEncoder {writer: wr};
    s.encode(&enc)
}

struct CompactEncoder {
    writer: @io::Writer,
}

fn write_compact_uint(w: @io::Writer, v: uint) {
    /*!
     *
     * Employs a utf-8 like scheme to write out a uint value,
     * assuming that such values are typically small.  For
     * each byte, we write out 7 bits and use the high bit to
     * indicate if another byte is needed.
     */

    let mut v = v;
    loop {
        let this_byte = (v & 0x7F) as u8;
        v = v >> 7;
        if v == 0 {
            w.write_u8(this_byte);
            return;
        }

        w.write_u8(this_byte | 0x80);
    }
}

fn read_compact_uint(r: @io::Reader) -> uint {
    /*!
     *
     * Inverse of `write_compact_uint`
     */

    let mut v: uint = 0;
    let mut shift: u8 = 0;
    loop {
        let this_byte = r.read_u8();
        v |= ((this_byte & 0x7F) as uint) << shift;
        if (this_byte & 0x80) == 0 {
            return v;
        }
        shift += 7;
    }
}

#[cfg(test)]
fn compact_uint_roundtrip(v0: uint) {
    let bytes = do io::with_bytes_writer |w| {
        write_compact_uint(w, v0);
    };

    let v1 = do io::with_bytes_reader(bytes) |r| {
        read_compact_uint(r)
    };

    assert_eq!(v0, v1);
}

#[test]
fn compact_uint_0() {
    compact_uint_roundtrip(0);
}

#[test]
fn compact_uint_22() {
    compact_uint_roundtrip(22);
}

#[test]
fn compact_uint_128() {
    compact_uint_roundtrip(128);
}

#[test]
fn compact_uint_3251() {
    compact_uint_roundtrip(3251);
}

#[test]
fn compact_uint_65535() {
    compact_uint_roundtrip(65535);
}

#[test]
fn compact_uint_99123551() {
    compact_uint_roundtrip(99123551);
}

#[test]
fn compact_uint_max() {
    compact_uint_roundtrip(::core::uint::max_value);
}

impl Encoder for CompactEncoder {
    fn emit_nil(&self) {}

    fn emit_uint(&self, +v: uint) {
        self.writer.write_le_uint(v)
    }
    fn emit_u64(&self, +v: u64) {
        self.writer.write_le_u64(v)
    }
    fn emit_u32(&self, +v: u32) {
        self.writer.write_le_u32(v)
    }
    fn emit_u16(&self, +v: u16) {
        self.writer.write_le_u16(v)
    }
    fn emit_u8(&self, +v: u8) {
        self.writer.write_u8(v)
    }

    fn emit_int(&self, +v: int) {
        self.writer.write_le_int(v)
    }
    fn emit_i64(&self, +v: i64) {
        self.writer.write_le_i64(v)
    }
    fn emit_i32(&self, +v: i32) {
        self.writer.write_le_i32(v)
    }
    fn emit_i16(&self, +v: i16) {
        self.writer.write_le_i16(v)
    }
    fn emit_i8(&self, +v: i8) {
        self.writer.write_i8(v)
    }

    fn emit_bool(&self, +v: bool) {
        self.writer.write_u8(v as u8)
    }

    fn emit_f64(&self, +v: f64) {
        self.writer.write_le_f64(v)
    }
    fn emit_f32(&self, +v: f32) {
        self.writer.write_le_f32(v)
    }
    fn emit_float(&self, +v: float) {
        self.writer.write_le_f64(v as f64)
    }

    fn emit_char(&self, +v: char) {
        self.writer.write_le_u32(v as u32)
    }

    fn emit_borrowed_str(&self, +v: &str) {
        write_compact_uint(self.writer, v.len());
        self.writer.write_str(v);
    }

    fn emit_owned_str(&self, +v: &str) {
        self.emit_borrowed_str(v)
    }

    fn emit_managed_str(&self, +v: &str) {
        self.emit_borrowed_str(v)
    }

    fn emit_borrowed(&self, &&f: &fn()) { f() }
    fn emit_owned(&self, &&f: &fn()) { f() }
    fn emit_managed(&self, &&f: &fn()) { f() }

    fn emit_enum(&self, _name: &str, &&f: &fn()) {
        f();
    }

    fn emit_enum_variant(&self, +_v_name: &str, +v_id: uint, +cnt: uint, &&f: &fn()) {
        fail_unless!(cnt < 256);
        write_compact_uint(self.writer, v_id);
        f();
    }

    fn emit_enum_variant_arg(&self, +_idx: uint, &&f: &fn()) {
        f();
    }

    fn emit_borrowed_vec(&self, +len: uint, &&f: &fn()) {
        write_compact_uint(self.writer, len);
        f();
    }

    fn emit_owned_vec(&self, +len: uint, &&f: &fn()) {
        self.emit_borrowed_vec(len, f)
    }

    fn emit_managed_vec(&self, +len: uint, &&f: &fn()) {
        self.emit_borrowed_vec(len, f)
    }

    fn emit_vec_elt(&self, +_idx: uint, &&f: &fn()) {
        f();
    }

    fn emit_rec(&self, &&f: &fn()) {
        f()
    }

    fn emit_struct(&self, +_name: &str, +_len: uint, &&f: &fn()) {
        f()
    }

    fn emit_field(&self, +_name: &str, +_idx: uint, &&f: &fn()) {
        f()
    }

    fn emit_tup(&self, +_len: uint, &&f: &fn()) {
        f()
    }

    fn emit_tup_elt(&self, +_idx: uint, &&f: &fn()) {
        f()
    }
}

pub fn decode<D:Decodable<CompactDecoder>>(doc: ebml::Doc) -> D {
    let bytes = vec::slice(*doc.data, doc.start, doc.data.len());
    do io::with_bytes_reader(bytes) |r| {
        let decoder = CompactDecoder {reader: r};
        Decodable::decode(&decoder)
    }
}

struct CompactDecoder<'self> {
    reader: @io::Reader
}

impl Decoder for CompactDecoder {
    fn read_nil(&self) -> () {}

    fn read_uint(&self) -> uint {
        self.reader.read_le_uint()
    }
    fn read_u64(&self) -> u64 {
        self.reader.read_le_u64()
    }
    fn read_u32(&self) -> u32 {
        self.reader.read_le_u32()
    }
    fn read_u16(&self) -> u16 {
        self.reader.read_le_u16()
    }
    fn read_u8(&self) -> u8 {
        self.reader.read_u8()
    }

    fn read_int(&self) -> int {
        self.reader.read_le_int()
    }
    fn read_i64(&self) -> i64 {
        self.reader.read_le_i64()
    }
    fn read_i32(&self) -> i32 {
        self.reader.read_le_i32()
    }
    fn read_i16(&self) -> i16 {
        self.reader.read_le_i16()
    }
    fn read_i8(&self) -> i8 {
        self.reader.read_i8()
    }

    fn read_bool(&self) -> bool {
        self.reader.read_u8() != 0
    }

    fn read_f64(&self) -> f64 {
        self.reader.read_le_f64()
    }
    fn read_f32(&self) -> f32 {
        self.reader.read_le_f32()
    }
    fn read_float(&self) -> float {
        self.reader.read_le_f64() as float
    }

    fn read_char(&self) -> char {
        self.reader.read_le_u32() as char
    }

    fn read_owned_str(&self) -> ~str {
        let len = read_compact_uint(self.reader);
        let bytes = self.reader.read_bytes(len);
        str::from_bytes(bytes)
    }

    fn read_managed_str(&self) -> @str {
        self.read_owned_str().to_managed()
    }

    fn read_owned<T>(&self, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_managed<T>(&self, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_enum<T>(&self, +_name: &str, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_enum_variant<T>(&self, &&f: &fn(+v: uint) -> T) -> T {
        let id = read_compact_uint(self.reader);
        f(id)
    }

    fn read_enum_variant_arg<T>(&self, +_idx: uint, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_owned_vec<T>(&self, &&f: &fn(+v: uint) -> T) -> T {
        let len = read_compact_uint(self.reader);
        f(len)
    }

    fn read_managed_vec<T>(&self, &&f: &fn(+v: uint) -> T) -> T {
        f(self.reader.read_le_uint())
    }

    fn read_vec_elt<T>(&self, +_idx: uint, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_rec<T>(&self, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_struct<T>(&self, +_name: &str, +_len: uint, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_field<T>(&self, +_name: &str, +_idx: uint, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_tup<T>(&self, +_len: uint, &&f: &fn() -> T) -> T {
        f()
    }

    fn read_tup_elt<T>(&self, +_idx: uint, &&f: &fn() -> T) -> T {
        f()
    }
}
