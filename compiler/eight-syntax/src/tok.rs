use eight_span::Span;
use std::fmt;
use std::fmt::{Debug, Formatter};

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

impl fmt::Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)
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
    KeywordIntrinsicScalar,
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

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TokenType::KeywordType => write!(f, "type"),
            TokenType::KeywordLet => write!(f, "let"),
            TokenType::KeywordFn => write!(f, "fn"),
            TokenType::KeywordIf => write!(f, "if"),
            TokenType::KeywordElse => write!(f, "else"),
            TokenType::KeywordReturn => write!(f, "return"),
            TokenType::KeywordBreak => write!(f, "break"),
            TokenType::KeywordContinue => write!(f, "continue"),
            TokenType::KeywordIntrinsicFn => write!(f, "intrinsic_fn"),
            TokenType::KeywordIntrinsicScalar => write!(f, "intrinsic_scalar"),
            TokenType::KeywordFor => write!(f, "for"),
            TokenType::KeywordNew => write!(f, "new"),
            TokenType::Identifier(v) => write!(f, "{}", v),
            TokenType::IntegerLiteral(v) => write!(f, "{}", v),
            TokenType::BooleanLiteral(v) => write!(f, "{}", v),
            TokenType::Comment(v) => write!(f, "{}", v),
            TokenType::AddressOf => write!(f, "&"),
            TokenType::Bang => write!(f, "!"),
            TokenType::Dot => write!(f, "."),
            TokenType::Plus => write!(f, "+"),
            TokenType::Star => write!(f, "*"),
            TokenType::Minus => write!(f, "-"),
            TokenType::Slash => write!(f, "/"),
            TokenType::Percent => write!(f, "%"),
            TokenType::Equal => write!(f, "="),
            TokenType::EqualEqual => write!(f, "=="),
            TokenType::LessThanEqual => write!(f, "<="),
            TokenType::GreaterThanEqual => write!(f, ">="),
            TokenType::BangEqual => write!(f, "!="),
            TokenType::OpenParen => write!(f, "("),
            TokenType::CloseParen => write!(f, ")"),
            TokenType::OpenBrace => write!(f, "{{"),
            TokenType::CloseBrace => write!(f, "}}"),
            TokenType::OpenBracket => write!(f, "["),
            TokenType::CloseBracket => write!(f, "]"),
            TokenType::OpenAngle => write!(f, "<"),
            TokenType::CloseAngle => write!(f, ">"),
            TokenType::Semicolon => write!(f, ";"),
            TokenType::Colon => write!(f, ":"),
            TokenType::ColonColon => write!(f, "::"),
            TokenType::Comma => write!(f, ","),
            TokenType::Arrow => write!(f, "->"),
            TokenType::LogicalAnd => write!(f, "&&"),
            TokenType::LogicalOr => write!(f, "||"),
            TokenType::Eof => Ok(()),
        }
    }
}

impl TokenType {
    pub fn is_integer_literal(&self) -> bool {
        matches!(self, TokenType::IntegerLiteral(_))
    }

    pub fn is_boolean_literal(&self) -> bool {
        matches!(self, TokenType::BooleanLiteral(_))
    }
}
