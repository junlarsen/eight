//! Error types for the parsing frontend.
//!
//! This module contains all the error types used by the parsing frontend. In order to reduce the
//! indirection between lexer and parser errors, we use the same error types for both. Furthermore,
//! this makes sense as the errors are produced incrementally.
//!
//! By this, we mean that because the lexer is an iterator over tokens, it doesn't necessarily know
//! of future lexer-related syntax errors. These will only be triggered by the parser upon
//! attempting to consume further tokens.
//!
//! Error codes follow the {namespace}{code} convention, where the namespace is a number that
//! represents the type of error, while {code} is a 3-digit number that represents the specific
//! error variant.
//!
//! - E1XXX: Token parsing errors

use crate::{Span, Token};
use miette::Diagnostic;
use thiserror::Error;

/// Utility macro for defining the [`ParserError`] enum type. It ensures that all variants have both
/// miette and thiserror diagnostic support.
macro_rules! define_error_variant {
    ($type_name:ident, [$($name:ident($ty:ty),)*]) => {
        #[derive(thiserror::Error, miette::Diagnostic, Debug)]
        #[error("error occured during parsing: {0}")]
        pub enum $type_name {
            $(
                #[error(transparent)]
                #[diagnostic(transparent)]
                $name(#[from] $ty),
            )*
        }
    }
}

define_error_variant!(
    ParseError,
    [
        UnexpectedEndOfInput(UnexpectedEndOfInputError),
        InvalidIntegerLiteral(InvalidIntegerLiteralError),
        UnexpectedCharacter(UnexpectedCharacterError),
        UnexpectedToken(UnexpectedTokenError),
    ]
);

/// Handy type alias for all parsing-related errors.
pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(E0101))]
#[error("expected more characters after this")]
pub struct UnexpectedEndOfInputError {
    // TODO: This span is completely broken
    #[label = "expected more characters after this"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(E0102))]
#[error("invalid 32-bit integer literal")]
pub struct InvalidIntegerLiteralError {
    pub buf: String,
    #[label("invalid 32-bit integer literal")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(E0103))]
#[error("did not expect {ch} in this position")]
pub struct UnexpectedCharacterError {
    pub ch: char,
    #[label("did not expect {ch} in this position")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(E0104))]
#[error("unexpected token")]
pub struct UnexpectedTokenError {
    pub token: Token,
    #[label("unexpected token")]
    pub span: Span,
}
