#![allow(unused_imports, unused_variables)]

use rustc_ast::token;
use rustc_ast::tokenstream::{DelimSpacing, DelimSpan, Spacing, TokenStream, TokenTree};
use rustc_errors::ErrorGuaranteed;
use rustc_expand::base::{AttrProcMacro, ExtCtxt};
use rustc_span::symbol::{sym, Symbol};
use rustc_span::Span;

pub(crate) struct ExpandRequires;

pub(crate) struct ExpandCaptures;

pub(crate) struct ExpandEnsures;

impl AttrProcMacro for ExpandRequires {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,	
    ) -> Result<TokenStream, ErrorGuaranteed> {
	todo!()
    }
}

impl AttrProcMacro for ExpandCaptures {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,	
    ) -> Result<TokenStream, ErrorGuaranteed> {
	todo!()
    }
}

impl AttrProcMacro for ExpandEnsures {
    fn expand<'cx>(
        &self,
        ecx: &'cx mut ExtCtxt<'_>,
        span: Span,
        annotation: TokenStream,
        annotated: TokenStream,	
    ) -> Result<TokenStream, ErrorGuaranteed> {
	todo!()
    }
}
