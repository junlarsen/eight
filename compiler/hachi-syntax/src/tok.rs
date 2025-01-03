use hachi_span::Span;
use std::fmt::Debug;

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
