use crate::{Span, Token, TokenType};
use miette::Diagnostic;
use std::iter::Peekable;
use std::str::CharIndices;
use thiserror::Error;

#[cfg_attr(test, derive(PartialEq))]
#[derive(Error, Diagnostic, Debug)]
pub enum LexerError {
    #[error("invalid integer literal: {buf}")]
    InvalidIntegerLiteral { buf: String, span: Span },
    #[error("unexpected character")]
    UnexpectedCharacter { ch: char, span: Span },
    #[error("unexpected end of input")]
    UnexpectedEndOfInput { span: Span },
    #[error("called next() on exhausted lexer source")]
    SourceExhausted,
    #[error("invalid state reached")]
    Infallible,
}

/// A lexer for source to token stream conversion.
#[derive(Debug)]
pub struct Lexer<'a> {
    input: Peekable<CharIndices<'a>>,
}

impl Lexer<'_> {
    /// Produce the next token from the input stream
    pub fn produce(&mut self) -> Result<Token, LexerError> {
        let (pos, ch) = self.input.next().ok_or(LexerError::SourceExhausted)?;
        match ch {
            '1'..='9' => self.produce_integer_literal(ch, pos),
            'a'..='z' | 'A'..='Z' | '_' => self.produce_keyword_or_identifier(ch, pos),
            // Single-character operators
            '.' => Ok(Token::new(TokenType::Dot, Span::pos(pos))),
            ';' => Ok(Token::new(TokenType::Semicolon, Span::pos(pos))),
            ',' => Ok(Token::new(TokenType::Comma, Span::pos(pos))),
            '+' => Ok(Token::new(TokenType::Plus, Span::pos(pos))),
            '*' => Ok(Token::new(TokenType::Star, Span::pos(pos))),
            '/' => Ok(Token::new(TokenType::Slash, Span::pos(pos))),
            '%' => Ok(Token::new(TokenType::Percent, Span::pos(pos))),
            // Double-character operations
            '=' => self.select_peek(pos, TokenType::Equal, |ch| match ch {
                '=' => Some(TokenType::EqualEqual),
                _ => None,
            }),
            '<' => self.select_peek(pos, TokenType::OpenAngle, |ch| match ch {
                '=' => Some(TokenType::LessThanEqual),
                _ => None,
            }),
            '>' => self.select_peek(pos, TokenType::CloseAngle, |ch| match ch {
                '=' => Some(TokenType::GreaterThanEqual),
                _ => None,
            }),
            '!' => self.select_peek(pos, TokenType::Bang, |ch| match ch {
                '=' => Some(TokenType::BangEqual),
                _ => None,
            }),
            ':' => self.select_peek(pos, TokenType::Colon, |ch| match ch {
                ':' => Some(TokenType::ColonColon),
                _ => None,
            }),
            '-' => self.select_peek(pos, TokenType::Minus, |ch| match ch {
                '>' => Some(TokenType::Arrow),
                _ => None,
            }),
            // Bracket pairs
            '(' => Ok(Token::new(TokenType::OpenParen, Span::pos(pos))),
            ')' => Ok(Token::new(TokenType::CloseParen, Span::pos(pos))),
            '[' => Ok(Token::new(TokenType::OpenBracket, Span::pos(pos))),
            ']' => Ok(Token::new(TokenType::CloseBracket, Span::pos(pos))),
            '{' => Ok(Token::new(TokenType::OpenBrace, Span::pos(pos))),
            '}' => Ok(Token::new(TokenType::CloseBrace, Span::pos(pos))),
            // Whitespace is consumed and ignored by the lexer.
            ' ' | '\t' | '\n' | '\r' => self.produce(),
            unrecognized_char => Err(LexerError::UnexpectedCharacter {
                ch: unrecognized_char,
                span: Span::pos(pos),
            }),
        }
    }

    /// Produce an integer literal token from the input stream.
    fn produce_integer_literal(&mut self, ch: char, pos: usize) -> Result<Token, LexerError> {
        let mut buf = vec![ch];
        // Consume while we're eating digits
        while matches!(self.input.peek(), Some((_, ch)) if ch.is_ascii_digit()) {
            let (_, ch) = self.input.next().ok_or(LexerError::Infallible)?;
            buf.push(ch);
        }
        let len = buf.len();
        let value = String::from_iter(buf);
        let integer =
            value
                .clone()
                .parse::<i32>()
                .map_err(|_| LexerError::InvalidIntegerLiteral {
                    buf: value,
                    span: Span::new(pos..pos + len),
                })?;
        Ok(Token::new(
            TokenType::IntegerLiteral(integer),
            Span::new(pos..pos + len),
        ))
    }

    /// Produce a keyword or identifier token from the input stream.
    fn produce_keyword_or_identifier(&mut self, ch: char, pos: usize) -> Result<Token, LexerError> {
        let mut buf = vec![ch];
        // Consume while we're eating alphanumeric characters
        while matches!(self.input.peek(), Some((_, ch)) if ch.is_ascii_alphanumeric() || ch == &'_')
        {
            let (_, ch) = self.input.next().ok_or(LexerError::Infallible)?;
            buf.push(ch);
        }
        let len = buf.len();
        let value = String::from_iter(buf);
        let ty = match value.as_str() {
            "type" => TokenType::KeywordType,
            "let" => TokenType::KeywordLet,
            "fn" => TokenType::KeywordFn,
            "if" => TokenType::KeywordIf,
            "else" => TokenType::KeywordElse,
            "return" => TokenType::KeywordReturn,
            "break" => TokenType::KeywordBreak,
            "continue" => TokenType::KeywordContinue,
            "for" => TokenType::KeywordFor,
            _ => TokenType::Identifier(value),
        };
        let span = Span::new(pos..pos + len);
        Ok(Token::new(ty, span))
    }
}

impl<'a> Lexer<'a> {
    /// Create a new lexer from a string.
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.char_indices().peekable(),
        }
    }

    /// Select the next token based on the current and next character
    pub fn select_peek<F>(
        &mut self,
        pos: usize,
        default: TokenType,
        f: F,
    ) -> Result<Token, LexerError>
    where
        F: FnOnce(&char) -> Option<TokenType>,
    {
        match self.input.peek() {
            Some((_, ch)) => match f(ch) {
                Some(typ) => {
                    let (next_post, _) = self.input.next().ok_or(LexerError::Infallible)?;
                    Ok(Token::new(typ, Span::new(pos..next_post + 1)))
                }
                None => Ok(Token::new(default, Span::pos(pos))),
            },
            _ => Ok(Token::new(default, Span::pos(pos))),
        }
    }
}

#[derive(Debug)]
pub struct LexerIter<'a> {
    l: Lexer<'a>,
}

impl<'a> Iterator for LexerIter<'a> {
    type Item = Result<Token, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.l.produce() {
            Err(LexerError::SourceExhausted) => None,
            v => Some(v),
        }
    }
}

impl<'a> IntoIterator for Lexer<'a> {
    type Item = Result<Token, LexerError>;
    type IntoIter = LexerIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        LexerIter { l: self }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, LexerError};
    use crate::{Span, Token, TokenType};

    macro_rules! assert_lexer_parse {
        ($input:expr, $($token:expr),*) => {
            let mut lexer = Lexer::new($input);
            $(
                let tok = lexer.produce().unwrap();
                assert_eq!(tok, $token);
            )*
            assert_eq!(Err(LexerError::SourceExhausted), lexer.produce());
        }
    }

    macro_rules! assert_failure {
        ($input:expr, $error:expr) => {
            let mut lexer = Lexer::new($input);
            assert_eq!(Err($error), lexer.produce());
        };
    }

    #[test]
    fn test_parse_integer_literal() {
        assert_lexer_parse!(
            "123",
            Token::new(TokenType::IntegerLiteral(123), Span::new(0..3))
        );
        assert_lexer_parse!(
            "123 123",
            Token::new(TokenType::IntegerLiteral(123), Span::new(0..3)),
            Token::new(TokenType::IntegerLiteral(123), Span::new(4..7))
        );
        // Cannot start with a zero in the current implementation.
        assert_failure!(
            "0123",
            LexerError::UnexpectedCharacter {
                ch: '0',
                span: Span::new(0..1)
            }
        );
        // Cannot be unparsable by rust's i32 parser
        assert_failure!(
            "99999999999999999999",
            LexerError::InvalidIntegerLiteral {
                buf: "99999999999999999999".to_string(),
                span: Span::new(0..20)
            }
        );
    }

    #[test]
    fn test_parse_keyword() {
        assert_lexer_parse!("type", Token::new(TokenType::KeywordType, Span::new(0..4)));
        assert_lexer_parse!("let", Token::new(TokenType::KeywordLet, Span::new(0..3)));
        // Non-keywords are turned into identifiers
        assert_lexer_parse!(
            "foo",
            Token::new(TokenType::Identifier("foo".to_string()), Span::new(0..3))
        );
        // Identifiers can contain underscores at any point
        assert_lexer_parse!(
            "foo_bar",
            Token::new(
                TokenType::Identifier("foo_bar".to_string()),
                Span::new(0..7)
            )
        );
        assert_lexer_parse!(
            "__foo",
            Token::new(TokenType::Identifier("__foo".to_string()), Span::new(0..5))
        );
        assert_lexer_parse!(
            "foo__",
            Token::new(TokenType::Identifier("foo__".to_string()), Span::new(0..5))
        );
    }

    #[test]
    fn test_parse_operators() {
        assert_lexer_parse!("+", Token::new(TokenType::Plus, Span::new(0..1)));
        assert_lexer_parse!("-", Token::new(TokenType::Minus, Span::new(0..1)));
        assert_lexer_parse!("*", Token::new(TokenType::Star, Span::new(0..1)));
    }

    #[test]
    fn test_parse_double_operators() {
        assert_lexer_parse!("==", Token::new(TokenType::EqualEqual, Span::new(0..2)));
        assert_lexer_parse!(
            "= =",
            Token::new(TokenType::Equal, Span::new(0..1)),
            Token::new(TokenType::Equal, Span::new(2..3))
        );
        assert_lexer_parse!("!=", Token::new(TokenType::BangEqual, Span::new(0..2)));
        assert_lexer_parse!("<=", Token::new(TokenType::LessThanEqual, Span::new(0..2)));
        assert_lexer_parse!(":", Token::new(TokenType::Colon, Span::new(0..1)));
        assert_lexer_parse!("::", Token::new(TokenType::ColonColon, Span::new(0..2)));
        assert_lexer_parse!(
            ": :",
            Token::new(TokenType::Colon, Span::new(0..1)),
            Token::new(TokenType::Colon, Span::new(2..3))
        );
        assert_lexer_parse!("->", Token::new(TokenType::Arrow, Span::new(0..2)));
    }
}
