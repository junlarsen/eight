//! Error types for the parsing frontend.
//!
//! This module contains all the error types used by the parsing frontend. In order to reduce the
//! indirection between lexer and parser errors, we use the same error types for both. Furthermore,
//! this makes sense as the errors are produced incrementally.
//!
//! By this, we mean that because the lexer is an iterator over tokens, it doesn't necessarily know
//! of future lexer-related syntax errors. These will only be triggered by the parser upon
//! attempting to consume further tokens.

use crate::{Span, Token};
use hachi_macros::declare_error_type;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("parser error: {0}")]
    pub enum ParseError {
        UnexpectedEndOfFile(UnexpectedEndOfFileError),
        InvalidIntegerLiteral(InvalidIntegerLiteralError),
        UnexpectedCharacter(UnexpectedCharacterError),
        UnexpectedToken(UnexpectedTokenError),
    }
}

/// Handy type alias for all parsing-related errors.
pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_end_of_file))]
#[error("expected more characters after this")]
pub struct UnexpectedEndOfFileError {
    // TODO: This span is completely broken
    #[label = "expected more characters after this"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::invalid_integer_literal))]
#[error("invalid 32-bit integer literal")]
pub struct InvalidIntegerLiteralError {
    pub buf: String,
    #[label("invalid 32-bit integer literal")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_character))]
#[error("did not expect {ch} in this position")]
pub struct UnexpectedCharacterError {
    pub ch: char,
    #[label("did not expect {ch} in this position")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_token))]
#[error("unexpected token")]
pub struct UnexpectedTokenError {
    pub token: Token,
    #[label("unexpected token")]
    pub span: Span,
}
