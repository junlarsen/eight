use std::ops::Range;

pub mod lexer;

/// Compact index of a character in the source code.
pub type SourcePosition = usize;

/// A span represents a range of characters in an input string.
///
/// It has the same semantics as Rust's x..y range syntax.
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
}
