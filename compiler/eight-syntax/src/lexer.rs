use crate::tok::{Token, TokenType};
use eight_support::context::{DiagnosticContext, ErrorGuaranteed};
use eight_support::errors::syntax::{
    InvalidIntegerLiteralError, UnexpectedCharacterError, UnfinishedTokenError,
};
use eight_support::ice;
use eight_support::span::{SourcePosition, Span};
use std::iter::Peekable;
use std::str::Chars;

pub struct LexerInput<'a> {
    input: Peekable<Chars<'a>>,
    pos: u32,
    dcx: &'a DiagnosticContext,
}

impl<'a> LexerInput<'a> {
    /// Create a new lexer from a string.
    pub fn new(input: &'a str, dcx: &'a DiagnosticContext) -> Self {
        Self {
            input: input.chars().peekable(),
            pos: 0,
            dcx,
        }
    }

    fn peek(&mut self) -> Option<&char> {
        self.input.peek()
    }

    /// Get the next character from the input stream.
    fn next(&mut self) -> Option<char> {
        if let Some(ch) = self.input.next() {
            self.pos += 1;
            return Some(ch);
        }
        None
    }

    pub fn pos(&self) -> u32 {
        self.pos
    }

    /// Expect the next character to be the given one, otherwise fail the lexer.
    ///
    /// This is useful for parsing two-character tokens that do not have a production on their own,
    /// such as '||'.
    fn expect_peek(
        &mut self,
        expected: char,
        start: SourcePosition,
        production: TokenType,
    ) -> Result<Token, ErrorGuaranteed> {
        let ch = self.peek().copied();
        let ch = ch.ok_or_else(|| {
            self.dcx.emit(UnfinishedTokenError {
                expected,
                span: Span::pos(start),
            })
        })?;
        match ch {
            c if c == expected => {
                self.next().unwrap_or_else(|| {
                    ice!("lexer should never fail to produce an already peeked token")
                });
                Ok(Token::new(production, Span::new(start..self.pos)))
            }
            _ => {
                if self.dcx.is_empty() {
                    self.dcx.emit(UnexpectedCharacterError {
                        ch,
                        // We are only reporting the position of the next character
                        span: Span::pos(start + 1),
                    });
                }
                Err(self.dcx.blanket())
            }
        }
    }

    /// Select the next token based on the current and next character
    ///
    /// This is useful for parsing tokens that may have a wider production based on the next
    /// character in the input stream. For example, the '&' character means deref-expr on its own,
    /// but may also be used as a logical and when followed by another '&'.
    fn select_peek<F>(&mut self, default: TokenType, start: SourcePosition, f: F) -> Token
    where
        F: FnOnce(&char) -> Option<TokenType>,
    {
        match self.peek() {
            Some(ch) => match f(ch) {
                Some(typ) => {
                    self.next().unwrap_or_else(|| {
                        ice!("lexer should never fail to produce an already peeked token")
                    });
                    Token::new(typ, Span::new(start..self.pos))
                }
                None => Token::new(default, Span::pos(start)),
            },
            _ => Token::new(default, Span::pos(start)),
        }
    }
}

/// A lexer for source to token stream conversion.
pub struct Lexer<'a> {
    input: LexerInput<'a>,
    dcx: &'a DiagnosticContext,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, dcx: &'a DiagnosticContext) -> Self {
        Self {
            input: LexerInput::new(input, dcx),
            dcx,
        }
    }

    pub fn pos(&self) -> u32 {
        self.input.pos()
    }

    /// Produce the next token from the input stream
    pub fn produce(&mut self) -> Option<Token> {
        let pos_before_eat = self.pos();
        let ch = self.input.next()?;
        match ch {
            '0'..='9' => self.produce_integer_literal(ch).ok(),
            'a'..='z' | 'A'..='Z' | '_' => Some(self.produce_keyword_or_identifier(ch)),
            // Single-character operators
            '.' => Some(Token::new(TokenType::Dot, Span::pos(pos_before_eat))),
            ';' => Some(Token::new(TokenType::Semicolon, Span::pos(pos_before_eat))),
            ',' => Some(Token::new(TokenType::Comma, Span::pos(pos_before_eat))),
            '+' => Some(Token::new(TokenType::Plus, Span::pos(pos_before_eat))),
            '*' => Some(Token::new(TokenType::Star, Span::pos(pos_before_eat))),
            '%' => Some(Token::new(TokenType::Percent, Span::pos(pos_before_eat))),
            '/' => match self.input.peek() {
                Some('/') => Some(self.produce_comment(ch)),
                _ => Some(Token::new(TokenType::Slash, Span::pos(pos_before_eat))),
            },
            // Double-character operations
            '=' => Some(
                self.input
                    .select_peek(TokenType::Equal, pos_before_eat, |ch| match ch {
                        '=' => Some(TokenType::EqualEqual),
                        _ => None,
                    }),
            ),
            '<' => Some(self.input.select_peek(
                TokenType::OpenAngle,
                pos_before_eat,
                |ch| match ch {
                    '=' => Some(TokenType::LessThanEqual),
                    _ => None,
                },
            )),
            '>' => Some(self.input.select_peek(
                TokenType::CloseAngle,
                pos_before_eat,
                |ch| match ch {
                    '=' => Some(TokenType::GreaterThanEqual),
                    _ => None,
                },
            )),
            '!' => Some(
                self.input
                    .select_peek(TokenType::Bang, pos_before_eat, |ch| match ch {
                        '=' => Some(TokenType::BangEqual),
                        _ => None,
                    }),
            ),
            ':' => Some(
                self.input
                    .select_peek(TokenType::Colon, pos_before_eat, |ch| match ch {
                        ':' => Some(TokenType::ColonColon),
                        _ => None,
                    }),
            ),
            '-' => Some(
                self.input
                    .select_peek(TokenType::Minus, pos_before_eat, |ch| match ch {
                        '>' => Some(TokenType::Arrow),
                        _ => None,
                    }),
            ),
            '&' => Some(self.input.select_peek(
                TokenType::AddressOf,
                pos_before_eat,
                |ch| match ch {
                    '&' => Some(TokenType::LogicalAnd),
                    _ => None,
                },
            )),
            '|' => self
                .input
                .expect_peek('|', pos_before_eat, TokenType::LogicalOr)
                .ok(),
            // Bracket pairs
            '(' => Some(Token::new(TokenType::OpenParen, Span::pos(pos_before_eat))),
            ')' => Some(Token::new(TokenType::CloseParen, Span::pos(pos_before_eat))),
            '[' => Some(Token::new(
                TokenType::OpenBracket,
                Span::pos(pos_before_eat),
            )),
            ']' => Some(Token::new(
                TokenType::CloseBracket,
                Span::pos(pos_before_eat),
            )),
            '{' => Some(Token::new(TokenType::OpenBrace, Span::pos(pos_before_eat))),
            '}' => Some(Token::new(TokenType::CloseBrace, Span::pos(pos_before_eat))),
            // Whitespace is consumed and ignored by the lexer.
            ' ' | '\t' | '\n' | '\r' => self.produce(),
            // Anything else is an obvious error
            unrecognized_char => {
                if self.dcx.is_empty() {
                    self.dcx.emit(UnexpectedCharacterError {
                        ch: unrecognized_char,
                        span: Span::pos(pos_before_eat),
                    });
                }
                None
            }
        }
    }

    /// Produce an integer literal token from the input stream.
    fn produce_integer_literal(&mut self, ch: char) -> Result<Token, ErrorGuaranteed> {
        // The incoming ch has already been consumed, so we offset by 1
        let start = self.input.pos() - 1;
        let mut buf = vec![ch];
        // Consume while we're eating digits
        while matches!(self.input.peek(), Some(ch) if ch.is_ascii_digit()) {
            let ch = self.input.next().unwrap_or_else(|| {
                ice!("lexer should never fail to produce an already peeked token")
            });
            buf.push(ch);
        }
        let value = String::from_iter(buf);
        if value.starts_with('0') && value.len() > 1 {
            return Err(self.dcx.emit(InvalidIntegerLiteralError {
                buf: value,
                span: Span::new(start..self.pos()),
            }));
        }

        let integer = value.clone().parse::<i32>().map_err(|_| {
            self.dcx.emit(InvalidIntegerLiteralError {
                buf: value,
                span: Span::new(start..self.pos()),
            })
        })?;
        Ok(Token::new(
            TokenType::IntegerLiteral(integer),
            Span::new(start..self.pos()),
        ))
    }

    /// Produce a comment token from the input stream.
    fn produce_comment(&mut self, ch: char) -> Token {
        // The incoming ch has already been consumed, so we offset by 1
        let start = self.input.pos() - 1;
        let fut = self
            .input
            .next()
            .unwrap_or_else(|| ice!("lexer should never fail to produce an already peeked token"));
        let mut buf = vec![ch, fut];

        // Must also consider that the newline doesn't come if the comment is the last token in the
        // file.
        while self.input.peek() != Some(&'\n') && self.input.peek().is_some() {
            let ch = self.input.next().unwrap_or_else(|| {
                ice!("lexer should never fail to produce an already peeked token")
            });
            buf.push(ch);
        }
        let value = String::from_iter(buf);
        Token::new(TokenType::Comment(value), Span::new(start..self.pos()))
    }

    /// Produce a keyword or identifier token from the input stream.
    fn produce_keyword_or_identifier(&mut self, ch: char) -> Token {
        // The incoming ch has already been consumed, so we offset by 1
        let start = self.input.pos() - 1;
        let mut buf = vec![ch];
        // Consume while we're eating alphanumeric characters
        while matches!(self.input.peek(), Some(ch) if ch.is_ascii_alphanumeric() || ch == &'_') {
            let ch = self.input.next().unwrap_or_else(|| {
                ice!("lexer should never fail to produce an already peeked token")
            });
            buf.push(ch);
        }

        let value = String::from_iter(buf);
        let ty = match value.as_str() {
            "struct" => TokenType::KeywordStruct,
            "let" => TokenType::KeywordLet,
            "fn" => TokenType::KeywordFn,
            "if" => TokenType::KeywordIf,
            "else" => TokenType::KeywordElse,
            "return" => TokenType::KeywordReturn,
            "break" => TokenType::KeywordBreak,
            "continue" => TokenType::KeywordContinue,
            "for" => TokenType::KeywordFor,
            "new" => TokenType::KeywordNew,
            "intrinsic_fn" => TokenType::KeywordIntrinsicFn,
            "intrinsic_type" => TokenType::KeywordIntrinsicType,
            "trait" => TokenType::KeywordTrait,
            "instance" => TokenType::KeywordInstance,
            "true" => TokenType::BooleanLiteral(true),
            "false" => TokenType::BooleanLiteral(false),
            _ => TokenType::Identifier(value),
        };
        let span = Span::new(start..self.pos());
        Token::new(ty, span)
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::tok::{Token, TokenType};
    use eight_support::span::Span;

    macro_rules! assert_lexer_parse {
        ($input:expr, $($token:expr),*) => {
            let src = std::rc::Rc::new(eight_support::context::DiagnosticSource::Stdin($input.to_owned()));
            let dcx = eight_support::context::DiagnosticContext::new(src.clone(), 16);
            let mut lexer = Lexer::new(src.as_ref().source(), &dcx);
            $(
                let tok = eight_macros::assert_some!(lexer.produce());
                assert_eq!(tok, $token);
            )*
            // Ensure there are no more tokens to be parsed
            eight_macros::assert_none!(lexer.produce())
        }
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
        assert_lexer_parse!(
            "0",
            Token::new(TokenType::IntegerLiteral(0), Span::new(0..1))
        );
    }

    #[test]
    fn test_parse_keyword() {
        assert_lexer_parse!(
            "struct",
            Token::new(TokenType::KeywordStruct, Span::new(0..6))
        );
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
        assert_lexer_parse!(
            "-> x",
            Token::new(TokenType::Arrow, Span::new(0..2)),
            Token::new(TokenType::Identifier("x".to_string()), Span::new(3..4))
        );
        assert_lexer_parse!(
            "- x",
            Token::new(TokenType::Minus, Span::new(0..1)),
            Token::new(TokenType::Identifier("x".to_string()), Span::new(2..3))
        );
        assert_lexer_parse!(
            "&& -",
            Token::new(TokenType::LogicalAnd, Span::new(0..2)),
            Token::new(TokenType::Minus, Span::new(3..4))
        );
        assert_lexer_parse!(
            "x   x",
            Token::new(TokenType::Identifier("x".to_string()), Span::new(0..1)),
            Token::new(TokenType::Identifier("x".to_string()), Span::new(4..5))
        );
    }

    #[test]
    fn test_parse_singular_term() {
        assert_lexer_parse!("&", Token::new(TokenType::AddressOf, Span::new(0..1)));
        assert_lexer_parse!("||", Token::new(TokenType::LogicalOr, Span::new(0..2)));
    }

    #[test]
    fn test_parse_comment() {
        assert_lexer_parse!(
            "// foo",
            Token::new(TokenType::Comment("// foo".to_string()), Span::new(0..6))
        );
        assert_lexer_parse!(
            "// foo\n",
            Token::new(TokenType::Comment("// foo".to_string()), Span::new(0..6))
        );
        assert_lexer_parse!(
            "// foo\n// bar",
            Token::new(TokenType::Comment("// foo".to_string()), Span::new(0..6)),
            Token::new(TokenType::Comment("// bar".to_string()), Span::new(7..13))
        );
    }
}
