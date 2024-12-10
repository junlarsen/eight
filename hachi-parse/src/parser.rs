use crate::lexer::{Lexer, LexerError, LexerIter};
use crate::syntax::{FunctionItem, Item, TranslationUnit, TypeItem};
use crate::{Token, TokenType};
use miette::Diagnostic;
use std::iter::Peekable;
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
pub enum ParseError {
    #[error("lexer error: {0}")]
    LexerError(#[from] LexerError),
    #[error("unexpected end of parse stream")]
    UnexpectedEndOfFile,
    #[error("unexpected token: {token:?}")]
    UnexpectedToken { token: Token },
}

pub type ParseResult<T> = Result<T, ParseError>;

pub struct Parser<'a> {
    lex: Peekable<LexerIter<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(lex: Lexer<'a>) -> Self {
        Self {
            lex: lex.into_iter().peekable(),
        }
    }

    pub fn has_next_token(&mut self) -> bool {
        self.lex.peek().is_none()
    }

    pub fn next_token(&mut self) -> ParseResult<Token> {
        self.lex
            .next()
            .ok_or(ParseError::UnexpectedEndOfFile)?
            .map_err(ParseError::LexerError)
    }
}

impl Parser<'_> {
    pub fn parse(&mut self) -> ParseResult<Box<TranslationUnit>> {
        self.parse_translation_unit()
    }

    pub fn parse_translation_unit(&mut self) -> ParseResult<Box<TranslationUnit>> {
        let mut items = Vec::new();
        while self.has_next_token() {
            items.push(self.parse_item()?);
        }
        Ok(Box::new(TranslationUnit { items }))
    }

    pub fn parse_item(&mut self) -> ParseResult<Box<Item>> {
        let fut = self.next_token()?;
        match fut.ty {
            TokenType::KeywordFn => self.parse_fn().map(|v| Box::new(Item::Function(v))),
            TokenType::KeywordType => self.parse_type().map(|v| Box::new(Item::Type(v))),
            _ => Err(ParseError::UnexpectedToken { token: fut }),
        }
    }

    pub fn parse_fn(&mut self) -> ParseResult<Box<FunctionItem>> {
        todo!()
    }

    pub fn parse_type(&mut self) -> ParseResult<Box<TypeItem>> {
        todo!()
    }
}
