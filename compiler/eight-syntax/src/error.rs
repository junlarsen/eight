//! Error types for the parsing frontend.
//!
//! This module contains all the error types used by the parsing frontend. In order to reduce the
//! indirection between lexer and parser errors, we use the same error types for both. Furthermore,
//! this makes sense as the errors are produced incrementally.
//!
//! By this, we mean that because the lexer is an iterator over tokens, it doesn't necessarily know
//! of future lexer-related syntax errors. These will only be triggered by the parser upon
//! attempting to consume further tokens.

use crate::Token;
use eight_macros::declare_error_type;
use eight_span::Span;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("parser error: {0}")]
    pub enum ParseError {
        UnexpectedEndOfFile(UnexpectedEndOfFileError),
        UnfinishedToken(UnfinishedTokenError),
        InvalidIntegerLiteral(InvalidIntegerLiteralError),
        UnexpectedCharacter(UnexpectedCharacterError),
        UnexpectedToken(UnexpectedTokenError),
    }
}

/// Handy type alias for all parsing-related errors.
pub type ParseResult<T> = Result<T, ParseError>;

/// Signals that the parser has reached the end of the input stream.
///
/// This error is only emitted to the diagnostic engine when the parser produces it. See the note
/// on [`Lexer::next`] for more information about how the parser handles this error once it is
/// emitted from the lexer.
///
/// It should also be noted that both lexer and parser produce this error in their signatures, but
/// as mentioned, only the parser emits it to the diagnostic engine.
#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(syntax::unexpected_end_of_file),
    help("add more input to form a valid program")
)]
#[error("expected more characters after this")]
pub struct UnexpectedEndOfFileError {
    #[label = "required more input to parse"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug, PartialEq)]
#[diagnostic(
    code(syntax::unfinished_token),
    help("did you forget to add a '{expected}' character here?")
)]
#[error("expected another '{expected}' character here")]
pub struct UnfinishedTokenError {
    pub expected: char,
    #[label = "this alone does not form a valid token"]
    pub span: Span,
}

const MAX_INTEGER_32_VALUE: i32 = i32::MAX;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(syntax::invalid_integer_literal),
    help("did you mean to specify a larger integer type?")
)]
#[error("found illegal i32 literal")]
pub struct InvalidIntegerLiteralError {
    pub buf: String,
    #[label("the maximum value that can be represented by an i32 is {MAX_INTEGER_32_VALUE}")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_character))]
#[error("found illegal character during parsing")]
pub struct UnexpectedCharacterError {
    pub ch: char,
    #[label("the character '{ch}' does not parse into any tokens")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_token))]
#[error("found unexpected token during parsing")]
pub struct UnexpectedTokenError {
    pub token: Token,
    #[label("was not expecting to find '{token}' in this position")]
    pub span: Span,
}
