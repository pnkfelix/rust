// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

The CodeMap tracks all the source code used within a single crate, mapping
from integer byte positions to the original source code location. Each bit of
source parsed during crate parsing (typically files, in-memory strings, or
various bits of macro expansion) cover a continuous range of bytes in the
CodeMap and are represented by FileMaps. Byte positions are stored in `spans`
and used pervasively in the compiler. They are absolute positions within the
CodeMap, which upon request can be converted to line and column information,
source code snippets, etc.

*/

extern mod extra;
use std::cmp;
use std::uint;
use extra::serialize::{Encodable, Decodable, Encoder, Decoder};

pub trait Pos {
    fn from_uint(n: uint) -> Self;
    fn to_uint(&self) -> uint;
}

/// A byte offset
#[deriving(Eq, Ord, IterBytes)]
pub struct BytePos(uint);

/// A character offset. Because of multibyte utf8 characters, a byte offset
/// is not equivalent to a character offset. The CodeMap will convert BytePos
/// values to CharPos values as necessary.
#[deriving(Eq, Ord, IterBytes)]
pub struct CharPos(uint);

// FIXME #4375: macro can remove the remaining duplication

impl Pos for BytePos {
    fn from_uint(n: uint) -> BytePos { BytePos(n) }
    fn to_uint(&self) -> uint { **self }
}

impl Add<BytePos, BytePos> for BytePos {
    fn add(&self, rhs: &BytePos) -> BytePos {
        BytePos(**self + **rhs)
    }
}

impl Sub<BytePos, BytePos> for BytePos {
    fn sub(&self, rhs: &BytePos) -> BytePos {
        BytePos(**self - **rhs)
    }
}

impl Pos for CharPos {
    fn from_uint(n: uint) -> CharPos { CharPos(n) }
    fn to_uint(&self) -> uint { **self }
}

impl Add<CharPos,CharPos> for CharPos {
    fn add(&self, rhs: &CharPos) -> CharPos {
        CharPos(**self + **rhs)
    }
}

impl Sub<CharPos,CharPos> for CharPos {
    fn sub(&self, rhs: &CharPos) -> CharPos {
        CharPos(**self - **rhs)
    }
}

/**
Spans represent a region of code, used for error reporting. Positions in spans
are *absolute* positions from the beginning of the codemap, not positions
relative to FileMaps. Methods on the CodeMap can be used to relate spans back
to the original source.
*/
#[deriving(IterBytes)]
pub struct span {
    lo: BytePos,
    hi: BytePos,
    expn_info: Option<@CallInfo>
}

pub static dummy_sp: span = span { lo: BytePos(0), hi: BytePos(0), expn_info: None };

#[deriving(Eq, Encodable, Decodable)]
pub struct spanned<T> { node: T, span: span }

impl cmp::Eq for span {
    fn eq(&self, other: &span) -> bool {
        return (*self).lo == (*other).lo && (*self).hi == (*other).hi;
    }
    fn ne(&self, other: &span) -> bool { !(*self).eq(other) }
}

impl<S:Encoder> Encodable<S> for span {
    /* Note #1972 -- spans are encoded but not decoded */
    fn encode(&self, s: &mut S) {
        s.emit_nil()
    }
}

impl<D:Decoder> Decodable<D> for span {
    fn decode(_d: &mut D) -> span {
        dummy_sp
    }
}

pub fn spanned<T>(lo: BytePos, hi: BytePos, t: T) -> spanned<T> {
    respan(mk_sp(lo, hi), t)
}

pub fn respan<T>(sp: span, t: T) -> spanned<T> {
    spanned {node: t, span: sp}
}

pub fn dummy_spanned<T>(t: T) -> spanned<T> {
    respan(dummy_sp, t)
}

/* assuming that we're not in macro expansion */
pub fn mk_sp(lo: BytePos, hi: BytePos) -> span {
    span {lo: lo, hi: hi, expn_info: None}
}

/// Information about a callee
#[deriving(IterBytes)]
pub struct CalleeInfo {
    /// name
    name: ~str,
    /// location
    span: Option<span>
}

/// Call information (also used in macro expansion)
#[deriving(IterBytes)]
pub struct CallInfo {
    call_site: span,
    callee: CalleeInfo
}

/// Identifies an offset of a multi-byte character in a FileMap
pub struct MultiByteChar {
    /// The absolute offset of the character in the CodeMap
    pos: BytePos,
    /// The number of bytes, >=2
    bytes: uint,
}

/// A single source in the CodeMap
pub struct FileMap {
    /// The name of the file that the source came from, source that doesn't
    /// originate from files has names between angle brackets by convention,
    /// e.g. `<anon>`
    name: ~str,
    /// The complete source code
    src: ~str,
    /// The start position of this source in the CodeMap
    start_pos: BytePos,
    /// Locations of lines beginnings in the source code
    lines: @mut ~[BytePos],
    /// Locations of multi-byte characters in the source code
    priv multibyte_chars: @mut ~[MultiByteChar],
}

impl FileMap {
    // EFFECT: register a start-of-line offset in the
    // table of line-beginnings.
    // UNCHECKED INVARIANT: these offsets must be added in the right
    // order and must be in the right places; there is shared knowledge
    // about what ends a line between this file and parse.rs
    pub fn next_line(&self, pos: BytePos) {
        // the new charpos must be > the last one (or it's the first one).
        let lines = self.lines;
        assert!((lines.len() == 0) || (lines[lines.len() - 1] < pos))
        lines.push(pos);
    }

    // get a line from the list of pre-computed line-beginnings
    pub fn get_line(&self, line: int) -> ~str {
        let begin: BytePos = self.lines[line] - self.start_pos;
        let begin = begin.to_uint();
        let slice = self.src.slice_from(begin);
        match slice.find('\n') {
            Some(e) => slice.slice_to(e).to_owned(),
            None => slice.to_owned()
        }
    }

    pub fn record_multibyte_char(&self, pos: BytePos, bytes: uint) {
        assert!(bytes >=2 && bytes <= 4);
        let mbc = MultiByteChar {
            pos: pos,
            bytes: bytes,
        };
        self.multibyte_chars.push(mbc);
    }
    
}

/// A 1-based index into the lines of a file
pub type Line = uint;

pub struct CodeMap {
    files: @mut ~[@FileMap]
}

/// A coordinate in a file
pub struct FileCoord {
    /// Line number (starts at 1)
    line: uint,
    /// Column number (starts at 0). Is a offset in characters, not bytes!
    column: uint
}

impl CodeMap {
    pub fn new() -> CodeMap {
        CodeMap {
            files: @mut ~[],
        }
    }

    /// Add a new FileMap to the CodeMap and return it
    pub fn new_filemap(&self, filename: ~str, src: ~str) -> @FileMap {
        let files = self.files;
        let start_pos = if files.len() == 0 {
            0
        } else {
            let last_start = files.last().start_pos.to_uint();
            let last_len = files.last().src.len();
            last_start + last_len
        };

        let filemap = @FileMap {
            name: filename,
            src: src,
            start_pos: BytePos(start_pos),
            lines: @mut ~[],
            multibyte_chars: @mut ~[],
        };

        files.push(filemap);
        filemap
    }

    /// Lookup source information about a BytePos
    pub fn lookup_char_pos(&self, pos: BytePos) -> FileCoord {
        let f = self.bytepos_to_filemap(pos);
        let a = self.lookup_line(pos);

        let line = a + 1; // Line numbers start at 1
        let chpos = self.bytepos_to_local_charpos(pos).to_uint();
        let linebpos = f.lines[a];
        let linechpos = self.bytepos_to_local_charpos(linebpos).to_uint();

        debug!("codemap: byte pos %? is on the line at byte pos %?",
               pos, linebpos);
        debug!("codemap: char pos %? is on the line at char pos %?",
               chpos, linechpos);
        debug!("codemap: byte is on line: %?", line);

        assert!(chpos >= linechpos.to_uint());
        FileCoord {
            line: line,
            column: chpos - linechpos
        }
    }

    pub fn span_to_str(&self, sp: span) -> ~str {
        let files = &self.files;
        if files.len() == 0 && sp == dummy_sp {
            return ~"no-location";
        }

        let lo = self.lookup_char_pos(sp.lo);
        let hi = self.lookup_char_pos(sp.hi);
        fmt!("%s:%u:%u: %u:%u", self.span_to_filename(sp), lo.line, lo.column, hi.line, hi.column)
    }

    pub fn span_to_filename(&self, sp: span) -> ~str {
        self.bytepos_to_filemap(sp.lo).src.clone()
    }

    pub fn span_to_filemap(&self, sp: span) -> @FileMap {
        self.bytepos_to_filemap(sp.lo)
    }

    pub fn span_to_lines(&self, sp: span) -> ~[Line] {
        let lo = self.lookup_char_pos(sp.lo);
        let hi = self.lookup_char_pos(sp.hi);
        let mut lines = ~[];
        for uint::range(lo.line - 1u, hi.line as uint) |i| {
            lines.push(i);
        };
        lines
    }

    pub fn span_to_snippet(&self, sp: span) -> ~str {
        let begin = self.lookup_byte_offset(sp.lo);
        let end = self.lookup_byte_offset(sp.hi);
        let (beginfile, endfile) = (self.bytepos_to_filemap(sp.lo), self.bytepos_to_filemap(sp.hi));

        assert_eq!(beginfile.start_pos, endfile.start_pos);
        return beginfile.src.slice(begin.to_uint(), end.to_uint()).to_owned();
    }

    pub fn filemap_from_name(&self, filename: &str) -> @FileMap {
        let fm = do self.files.iter().find_ |fm| { filename == fm.name };
        *fm.expect(fmt!("asking for %s which we don't know about", filename))
    }

    fn lookup_filemap_idx(&self, pos: BytePos) -> uint {
        let files = &self.files;
        let len = files.len();
        let mut a = 0u;
        let mut b = len;
        while b - a > 1u {
            let m = (a + b) / 2u;
            if self.files[m].start_pos > pos {
                b = m;
            } else {
                a = m;
            }
        }
        if (a >= len) {
            fail!("position %u does not resolve to a source location", pos.to_uint())
        }

        return a;
    }

    fn bytepos_to_filemap(&self, b: BytePos) -> @FileMap {
        self.files[self.lookup_filemap_idx(b)]
    }

    pub fn lookup_line(&self, pos: BytePos) -> Line {
        let f = self.bytepos_to_filemap(pos);
        let mut a = 0u;
        let lines = &f.lines;
        let mut b = lines.len();
        while b - a > 1u {
            let m = (a + b) / 2u;
            if lines[m] > pos { b = m; } else { a = m; }
        }
        a
    }

    fn lookup_byte_offset(&self, bpos: BytePos) -> BytePos {
        let fm = self.bytepos_to_filemap(bpos);
        bpos - fm.start_pos
    }

    // Converts an absolute BytePos to a CharPos relative to the file it is
    // located in
    fn bytepos_to_local_charpos(&self, bpos: BytePos) -> CharPos {
        debug!("codemap: converting %? to char pos", bpos);
        let map = self.bytepos_to_filemap(bpos);

        // The number of extra bytes due to multibyte chars in the FileMap
        let mut total_extra_bytes = 0;

        for map.multibyte_chars.iter().advance |mbc| {
            debug!("codemap: %?-byte char at %?", mbc.bytes, mbc.pos);
            if mbc.pos < bpos {
                total_extra_bytes += mbc.bytes;
                // We should never see a byte position in the middle of a
                // character
                assert!(bpos == mbc.pos
                    || bpos.to_uint() >= mbc.pos.to_uint() + mbc.bytes);
            } else {
                break;
            }
        }

        CharPos(bpos.to_uint() - total_extra_bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn t1 () {
        let mut cm = CodeMap::new();
        let fm = cm.new_filemap(~"blork.rs", ~"first line.\nsecond line");
        fm.next_line(BytePos(0));
        assert_eq!(fm.get_line(0), ~"first line.");
        // TESTING BROKEN BEHAVIOR:
        fm.next_line(BytePos(10));
        assert_eq!(fm.get_line(1), ~".");
    }

    #[test]
    #[should_fail]
    fn t2 () {
        let mut cm = CodeMap::new();
        let fm = cm.new_filemap(~"blork.rs", ~"first line.\nsecond line");
        // TESTING *REALLY* BROKEN BEHAVIOR:
        fm.next_line(BytePos(0));
        fm.next_line(BytePos(10));
        fm.next_line(BytePos(2));
    }
}
