use std::ops::Range;

pub mod ast;
pub mod lexer;
pub mod parser;

/// Compact index of a character in the source code.
pub type SourcePosition = usize;

/// A span represents a range of characters in an input string.
///
/// It has the same semantics as Rust's x..y range syntax.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct Span {
    pub low: SourcePosition,
    pub high: SourcePosition,
}

impl Span {
    /// Create a new span from the low and high positions.
    pub fn new(range: Range<SourcePosition>) -> Self {
        Self {
            low: range.start,
            high: range.end,
        }
    }

    /// Create a new span from a single position.
    pub fn pos(low: SourcePosition) -> Self {
        Self { low, high: low + 1 }
    }
}

impl From<Range<SourcePosition>> for Span {
    fn from(range: Range<SourcePosition>) -> Self {
        Self::new(range)
    }
}

/// A single token parsed from the source code.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub span: Span,
    pub ty: TokenType,
}

impl Token {
    /// Create a new token from a span and a token type.
    pub fn new(ty: TokenType, span: Span) -> Self {
        Self { span, ty }
    }
}

/// Enumeration of all possible token types.
///
/// Some variants hold values such as literals and identifiers.
///
/// We currently only support i32 integer literals as the only data type.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    KeywordType,
    KeywordLet,
    KeywordFn,
    KeywordIf,
    KeywordElse,
    KeywordReturn,
    KeywordBreak,
    KeywordContinue,
    KeywordFor,

    Identifier(String),
    IntegerLiteral(i32),
    Comment(String),

    Deref,
    Bang,
    Dot,
    Plus,
    Star,
    Minus,
    Slash,
    Equal,
    EqualEqual,
    LessThanEqual,
    GreaterThanEqual,
    BangEqual,
    Percent,

    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    OpenAngle,
    CloseAngle,

    Semicolon,
    Colon,
    ColonColon,
    Comma,
    Arrow,
    LogicalAnd,
    LogicalOr,

    Eof,
}

#[cfg(test)]
mod assertions {
    /// Assert that a `Result` is `Ok`, returning the value inside the `Ok` variant.
    #[macro_export]
    macro_rules! assert_ok {
        ($expr:expr) => {{
            match $expr {
                ::std::result::Result::Ok(val) => val,
                ::std::result::Result::Err(err) => {
                    panic!("assertion failed: Err({:?})", err);
                }
            }
        }};
    }

    /// Assert that a `Result` is `Err`, returning the error inside the `Err` variant.
    #[macro_export]
    macro_rules! assert_err {
        ($expr:expr) => {{
            match $expr {
                ::std::result::Result::Ok(val) => {
                    panic!("assertion failed: Ok({:?})", val);
                }
                ::std::result::Result::Err(err) => err,
            }
        }};
    }

    /// Assert that an `Option` is `Some`, returning the value inside the `Some` variant.
    #[macro_export]
    macro_rules! assert_some {
        ($expr:expr) => {{
            match $expr {
                ::std::option::Option::Some(val) => val,
                ::std::option::Option::None => {
                    panic!("assertion failed: None");
                }
            }
        }};
    }

    /// Assert that an `Option` is `None`.
    #[macro_export]
    macro_rules! assert_none {
        ($expr:expr) => {{
            if let ::std::option::Option::Some(val) = $expr {
                panic!("assertion failed: Some({:?})", val);
            };
        }};
    }
}
