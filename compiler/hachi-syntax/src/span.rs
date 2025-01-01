use miette::{SourceOffset, SourceSpan};
use std::cmp::{max, min};
use std::fmt::Debug;
use std::ops::Range;

/// Compact index of a character in the source code.
pub type SourcePosition = usize;

/// A span represents a range of characters in an input string.
///
/// It has the same semantics as Rust's x..y range syntax.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct Span {
    pub low: SourcePosition,
    pub high: SourcePosition,
}

impl From<Span> for SourceSpan {
    fn from(val: Span) -> Self {
        SourceSpan::new(SourceOffset::from(val.low), val.high - val.low)
    }
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

    /// Create a new span from two positions.
    pub fn from_pair(low: &Span, high: &Span) -> Self {
        low.merge(high)
    }

    pub fn empty() -> Self {
        Self { low: 0, high: 0 }
    }

    /// Get the union of two spans.
    ///
    /// This is equivalent to `min(self.low, other.low)..max(self.high, other.high)`. This method is
    /// particularly useful when combining spans from two relevant tokens.
    ///
    /// ```
    /// use hachi_syntax::Span;
    ///
    /// let a = Span::new(0..10);
    /// let b = Span::new(5..15);
    /// let c = a.merge(&b);
    /// assert_eq!(c, Span::new(0..15));
    /// ```
    pub fn merge(&self, other: &Self) -> Self {
        let low = min(self.low, other.low);
        let high = max(self.high, other.high);
        Self { low, high }
    }
}

impl From<Range<SourcePosition>> for Span {
    fn from(range: Range<SourcePosition>) -> Self {
        Self::new(range)
    }
}

/// A single token parsed from the source code.
///
/// TODO: Consider if it's worth interning the spans as they are copied a lot around in the AST.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    KeywordType,
    KeywordIntrinsicType,
    KeywordLet,
    KeywordFn,
    KeywordIntrinsicFn,
    KeywordIf,
    KeywordElse,
    KeywordReturn,
    KeywordBreak,
    KeywordContinue,
    KeywordFor,
    KeywordNew,

    Identifier(String),
    IntegerLiteral(i32),
    BooleanLiteral(bool),
    Comment(String),

    AddressOf,
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

impl TokenType {
    pub fn is_integer_literal(&self) -> bool {
        matches!(self, TokenType::IntegerLiteral(_))
    }

    pub fn is_boolean_literal(&self) -> bool {
        matches!(self, TokenType::BooleanLiteral(_))
    }
}
