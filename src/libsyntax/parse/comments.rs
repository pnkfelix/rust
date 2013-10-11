// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast;
use parse::lexer::{is_line_non_doc_comment, is_block_non_doc_comment};

use std::uint;

// Issue #3195: these should probably be factored out of libsyntax and
// into separate libpprust.
pub use self::comments::just_for_pprust::gather_comments_and_literals;
pub use self::comments::just_for_pprust::{cmnt,lit,cmnt_style};
pub use self::comments::just_for_pprust::{isolated,trailing,mixed,blank_line};

mod comments {
    pub mod just_for_pprust;
}

pub fn is_doc_comment(s: &str) -> bool {
    (s.starts_with("///") && !is_line_non_doc_comment(s)) ||
    s.starts_with("//!") ||
    (s.starts_with("/**") && !is_block_non_doc_comment(s)) ||
    s.starts_with("/*!")
}

pub fn doc_comment_style(comment: &str) -> ast::AttrStyle {
    assert!(is_doc_comment(comment));
    if comment.starts_with("//!") || comment.starts_with("/*!") {
        ast::AttrInner
    } else {
        ast::AttrOuter
    }
}

pub fn strip_doc_comment_decoration(comment: &str) -> ~str {

    /// remove whitespace-only lines from the start/end of lines
    fn vertical_trim(lines: ~[~str]) -> ~[~str] {
        let mut i = 0u;
        let mut j = lines.len();
        // first line of all-stars should be omitted
        if lines.len() > 0 && lines[0].iter().all(|c| c == '*') {
            i += 1;
        }
        while i < j && lines[i].trim().is_empty() {
            i += 1;
        }
        // like the first, a last line of all stars should be omitted
        if j > i && lines[j - 1].iter().skip(1).all(|c| c == '*') {
            j -= 1;
        }
        while j > i && lines[j - 1].trim().is_empty() {
            j -= 1;
        }
        return lines.slice(i, j).to_owned();
    }

    /// remove a "[ \t]*\*" block from each line, if possible
    fn horizontal_trim(lines: ~[~str]) -> ~[~str] {
        let mut i = uint::max_value;
        let mut can_trim = true;
        let mut first = true;
        for line in lines.iter() {
            for (j, c) in line.iter().enumerate() {
                if j > i || !"* \t".contains_char(c) {
                    can_trim = false;
                    break;
                }
                if c == '*' {
                    if first {
                        i = j;
                        first = false;
                    } else if i != j {
                        can_trim = false;
                    }
                    break;
                }
            }
            if i > line.len() {
                can_trim = false;
            }
            if !can_trim {
                break;
            }
        }

        if can_trim {
            do lines.map |line| {
                line.slice(i + 1, line.len()).to_owned()
            }
        } else {
            lines
        }
    }

    // one-line comments lose their prefix
    static ONLINERS: &'static [&'static str] = &["///!", "///", "//!", "//"];
    for prefix in ONLINERS.iter() {
        if comment.starts_with(*prefix) {
            return comment.slice_from(prefix.len()).to_owned();
        }
    }

    if comment.starts_with("/*") {
        let lines = comment.slice(3u, comment.len() - 2u)
            .any_line_iter()
            .map(|s| s.to_owned())
            .collect::<~[~str]>();

        let lines = vertical_trim(lines);
        let lines = horizontal_trim(lines);

        return lines.connect("\n");
    }

    fail2!("not a doc-comment: {}", comment);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test] fn test_block_doc_comment_1() {
        let comment = "/**\n * Test \n **  Test\n *   Test\n*/";
        let stripped = strip_doc_comment_decoration(comment);
        assert_eq!(stripped, ~" Test \n*  Test\n   Test");
    }

    #[test] fn test_block_doc_comment_2() {
        let comment = "/**\n * Test\n *  Test\n*/";
        let stripped = strip_doc_comment_decoration(comment);
        assert_eq!(stripped, ~" Test\n  Test");
    }

    #[test] fn test_block_doc_comment_3() {
        let comment = "/**\n let a: *int;\n *a = 5;\n*/";
        let stripped = strip_doc_comment_decoration(comment);
        assert_eq!(stripped, ~" let a: *int;\n *a = 5;");
    }

    #[test] fn test_block_doc_comment_4() {
        let comment = "/*******************\n test\n *********************/";
        let stripped = strip_doc_comment_decoration(comment);
        assert_eq!(stripped, ~" test");
    }

    #[test] fn test_line_doc_comment() {
        let stripped = strip_doc_comment_decoration("/// test");
        assert_eq!(stripped, ~" test");
        let stripped = strip_doc_comment_decoration("///! test");
        assert_eq!(stripped, ~" test");
        let stripped = strip_doc_comment_decoration("// test");
        assert_eq!(stripped, ~" test");
        let stripped = strip_doc_comment_decoration("// test");
        assert_eq!(stripped, ~" test");
        let stripped = strip_doc_comment_decoration("///test");
        assert_eq!(stripped, ~"test");
        let stripped = strip_doc_comment_decoration("///!test");
        assert_eq!(stripped, ~"test");
        let stripped = strip_doc_comment_decoration("//test");
        assert_eq!(stripped, ~"test");
    }
}
