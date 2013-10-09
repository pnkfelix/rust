// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast;
use codemap::{spanned, Spanned, mk_sp};
use parse::common::*; //resolve bug?
use parse::token;
use parse::parser::Parser;
use parse::token::INTERPOLATED;

// a parser that can parse attributes.
pub trait parser_attr {
    fn parse_outer_attributes(&self) -> ~[ast::Attribute];
    fn parse_attribute(&self, permit_inner: bool) -> ast::Attribute;
    fn parse_inner_attrs_and_next(&self) ->
        (~[ast::Attribute], ~[ast::Attribute]);
    fn parse_meta_item(&self) -> @ast::MetaItem;
    fn parse_meta_seq(&self) -> ~[@ast::MetaItem];
    fn parse_optional_meta(&self) -> ~[@ast::MetaItem];
}

// Does token after `#` start some attribute?  Also, if `permit_inner`
// then accept inner or outer attributes; otherwise solely outer.
fn second_token_of_attr(t:&token::Token, permit_inner: bool) -> bool {
    if permit_inner {
        *t == token::LBRACKET || *t == token::NOT || token::is_ident(t)
    } else {
        *t == token::LBRACKET || token::is_ident(t)
    }
}

impl parser_attr for Parser {

    // Parse attributes that appear before an item
    fn parse_outer_attributes(&self) -> ~[ast::Attribute] {
        let mut attrs: ~[ast::Attribute] = ~[];
        loop {
            debug2!("parse_outer_attributes: self.token={:?}",
                   self.token);
            match *self.token {
              token::INTERPOLATED(token::nt_attr(*)) => {
                attrs.push(self.parse_attribute(false));
              }
              token::POUND => {
                if self.look_ahead(1, |t| !second_token_of_attr(t, false)) {
                    break;
                }
                attrs.push(self.parse_attribute(false));
              }
              token::DOC_COMMENT(s) => {
                let attr = ::attr::mk_sugared_doc_attr(
                    self.id_to_str(s),
                    self.span.lo,
                    self.span.hi
                );
                if attr.node.style != ast::AttrOuter {
                  self.fatal("expected outer comment");
                }
                attrs.push(attr);
                self.bump();
              }
              _ => break
            }
        }
        return attrs;
    }

    // matches old (deprecated) and new attribute syntax:
    //   old, outer attribute:  # [ meta_item ]
    //   old, inner attribute:  # [ meta_item ] ;
    //   new, outer attribute:  #   meta_item
    //   new, inner attribute:  # ! meta_item   ;
    //
    // if permit_inner, then allowed to match either inner attribute
    // case above (and a trailing `;` indicates an inner attribute).
    // If not permit_inner, then parses `#[meta_item]` as an outer
    // attribute (without looking ahead to see if semicolon follows).
    fn parse_attribute(&self, permit_inner: bool) -> ast::Attribute {
        debug2!("parse_attributes: permit_inner={:?} self.token={:?}",
               permit_inner, self.token);
        enum AttrStyle { Indeterminate, MustBeInner, MustBeOuter };
        let mut style_req = Indeterminate;
        let (span, value) = match *self.token {
            INTERPOLATED(token::nt_attr(attr)) => {
                assert!(attr.node.style == ast::AttrOuter);
                self.bump();
                (attr.span, attr.node.value)
            }
            token::POUND => {
                let lo = self.span.lo;
                self.bump();
                let meta_item;
                if *self.token == token::LBRACKET {
                    self.expect(&token::LBRACKET);
                    meta_item = self.parse_meta_item();
                    self.expect(&token::RBRACKET);
                } else {
                    if *self.token == token::NOT {
                        if !permit_inner {
                            self.fatal(format!("Expected outer attribute \
                                                but found `{}`",
                                               self.this_token_to_str()));
                        }
                        style_req = MustBeInner;
                        self.bump();
                    } else {
                        style_req = MustBeOuter;
                    }
                    meta_item = self.parse_meta_item();
                }
                let hi = self.span.hi;
                (mk_sp(lo, hi), meta_item)
            }
            _ => {
                self.fatal(format!("expected `\\#` but found `{}`",
                                   self.this_token_to_str()));
            }
        };
        let style = match style_req {
            Indeterminate => {
                if permit_inner && *self.token == token::SEMI {
                    self.bump();
                    ast::AttrInner
                } else {
                    ast::AttrOuter
                }
            }
            MustBeInner => {
                self.expect(&token::SEMI);
                ast::AttrInner
            }
            MustBeOuter => {
                if *self.token == token::SEMI {
                    self.fatal(format!("expected item or another attribute \
                                        but found `{}`",
                                       self.this_token_to_str()));
                }
                ast::AttrOuter
            }
        };
        return Spanned {
            span: span,
            node: ast::Attribute_ {
                style: style,
                value: value,
                is_sugared_doc: false
            }
        };
    }

    // Parse attributes that appear after the opening of an item, each
    // terminated by a semicolon. In addition to a vector of inner attributes,
    // this function also returns a vector that may contain the first outer
    // attribute of the next item (since we can't know whether the attribute
    // is an inner attribute of the containing item or an outer attribute of
    // the first contained item until we see the semi).

    // matches inner_attrs* outer_attr?
    // you can make the 'next' field an Option, but the result is going to be
    // more useful as a vector.
    fn parse_inner_attrs_and_next(&self)
                                  -> (~[ast::Attribute], ~[ast::Attribute]) {
        let mut inner_attrs: ~[ast::Attribute] = ~[];
        let mut next_outer_attrs: ~[ast::Attribute] = ~[];
        loop {
            let attr = match *self.token {
                token::INTERPOLATED(token::nt_attr(*)) => {
                    self.parse_attribute(true)
                }
                token::POUND => {
                    if self.look_ahead(1, |t| !second_token_of_attr(t, true)) {
                        // This is an extension
                        break;
                    }
                    self.parse_attribute(true)
                }
                token::DOC_COMMENT(s) => {
                    self.bump();
                    ::attr::mk_sugared_doc_attr(self.id_to_str(s),
                                                self.span.lo,
                                                self.span.hi)
                }
                _ => {
                    break;
                }
            };
            if attr.node.style == ast::AttrInner {
                inner_attrs.push(attr);
            } else {
                next_outer_attrs.push(attr);
                break;
            }
        }
        (inner_attrs, next_outer_attrs)
    }

    // matches meta_item = IDENT
    // | IDENT = lit
    // | IDENT meta_seq
    fn parse_meta_item(&self) -> @ast::MetaItem {
        let lo = self.span.lo;
        let name = self.id_to_str(self.parse_ident());
        match *self.token {
            token::EQ => {
                self.bump();
                let lit = self.parse_lit();
                let hi = self.span.hi;
                @spanned(lo, hi, ast::MetaNameValue(name, lit))
            }
            token::LPAREN => {
                let inner_items = self.parse_meta_seq();
                let hi = self.span.hi;
                @spanned(lo, hi, ast::MetaList(name, inner_items))
            }
            _ => {
                let hi = self.last_span.hi;
                @spanned(lo, hi, ast::MetaWord(name))
            }
        }
    }

    // matches meta_seq = ( COMMASEP(meta_item) )
    fn parse_meta_seq(&self) -> ~[@ast::MetaItem] {
        self.parse_seq(&token::LPAREN,
                       &token::RPAREN,
                       seq_sep_trailing_disallowed(token::COMMA),
                       |p| p.parse_meta_item()).node
    }

    fn parse_optional_meta(&self) -> ~[@ast::MetaItem] {
        match *self.token {
            token::LPAREN => self.parse_meta_seq(),
            _ => ~[]
        }
    }
}
