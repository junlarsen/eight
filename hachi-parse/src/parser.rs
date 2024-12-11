use crate::lexer::{Lexer, LexerError, LexerIter};
use crate::syntax::{
    FunctionItem, Identifier, Integer32Type, Item, NamedType, PointerType, TranslationUnit, Type,
    TypeItem, TypeMemberItem, UnitType,
};
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

    /// Check if there are any more tokens in the source.
    pub fn has_next_token(&mut self) -> bool {
        self.lex.peek().is_none()
    }

    /// Advance the lexer iterator by one, and return the advanced token.
    pub fn next_token(&mut self) -> ParseResult<Token> {
        self.lex
            .next()
            .ok_or(ParseError::UnexpectedEndOfFile)?
            .map_err(ParseError::LexerError)
    }

    /// Peek at the next token in the source without consuming it.
    pub fn peek_token(&mut self) -> ParseResult<Option<&Token>> {
        let tok = self.lex.peek();
        let tok = tok.map_or(Ok(None), |t| t.as_ref().map(Some));
        tok.map_err(|v| ParseError::LexerError(v.clone()))
    }

    /// Determine if the next token in the token stream matches the given type.
    pub fn peek_token_match(&mut self, ty: TokenType) -> ParseResult<bool> {
        let token = self.peek_token()?;
        match token {
            Some(token) if token.ty == ty => Ok(true),
            _ => Ok(false),
        }
    }

    /// Consume the next token from the token stream and ensure it matches the given type.
    ///
    /// If the token doesn't match, the entire parser fails.
    pub fn expect_token(&mut self, ty: TokenType) -> ParseResult<Token> {
        let token = self.next_token()?;
        match token {
            token if token.ty == ty => Ok(token),
            _ => Err(ParseError::UnexpectedToken { token }),
        }
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
        let token = self.peek_token()?.ok_or(ParseError::UnexpectedEndOfFile)?;
        match token.ty {
            TokenType::KeywordFn => self.parse_fn_item().map(|v| Box::new(Item::Function(v))),
            TokenType::KeywordType => self.parse_type_item().map(|v| Box::new(Item::Type(v))),
            _ => Err(ParseError::UnexpectedToken {
                token: self.next_token()?,
            }),
        }
    }

    pub fn parse_fn_item(&mut self) -> ParseResult<Box<FunctionItem>> {
        todo!()
    }

    pub fn parse_type_item(&mut self) -> ParseResult<Box<TypeItem>> {
        self.expect_token(TokenType::KeywordType)?;
        let id = self.parse_identifier()?;
        self.expect_token(TokenType::Equal)?;
        self.expect_token(TokenType::OpenBrace)?;
        let mut members = Vec::new();
        while !self.peek_token_match(TokenType::CloseBrace)? {
            members.push(self.parse_type_member_item()?);
        }
        self.expect_token(TokenType::CloseBrace)?;
        Ok(Box::new(TypeItem {
            span: id.span.clone(),
            name: id,
            members,
        }))
    }

    pub fn parse_type_member_item(&mut self) -> ParseResult<Box<TypeMemberItem>> {
        let id = self.parse_identifier()?;
        self.expect_token(TokenType::Colon)?;
        let ty = self.parse_type()?;
        self.expect_token(TokenType::Comma)?;
        Ok(Box::new(TypeMemberItem {
            span: id.span.clone(),
            name: id,
            r#type: ty,
        }))
    }

    pub fn parse_identifier(&mut self) -> ParseResult<Box<Identifier>> {
        let token = self.next_token()?;
        match token {
            Token {
                ty: TokenType::Identifier(id),
                span,
            } => Ok(Box::new(Identifier { name: id, span })),
            _ => Err(ParseError::UnexpectedToken { token }),
        }
    }

    pub fn parse_type(&mut self) -> ParseResult<Box<Type>> {
        let token = self.peek_token()?.ok_or(ParseError::UnexpectedEndOfFile)?;
        match &token.ty {
            // If it is a named type, we can test if it's matching one of the builtin types.
            TokenType::Identifier(v) => match v.as_str() {
                "i32" => {
                    let id = self.parse_identifier()?;
                    Ok(Box::new(Type::Integer32(Box::new(Integer32Type {
                        span: id.span,
                    }))))
                }
                "void" => {
                    let id = self.parse_identifier()?;
                    Ok(Box::new(Type::Unit(Box::new(UnitType { span: id.span }))))
                }
                _ => Ok(Box::new(Type::Named(self.parse_named_type()?))),
            },
            TokenType::Star => Ok(Box::new(Type::Pointer(self.parse_pointer_type()?))),
            _ => Err(ParseError::UnexpectedToken {
                token: self.next_token()?,
            }),
        }
    }

    pub fn parse_named_type(&mut self) -> ParseResult<Box<NamedType>> {
        let id = self.parse_identifier()?;
        Ok(Box::new(NamedType {
            span: id.span.clone(),
            name: id,
        }))
    }

    pub fn parse_pointer_type(&mut self) -> ParseResult<Box<PointerType>> {
        let indirection = self.expect_token(TokenType::Star)?;
        let inner = self.parse_type()?;
        Ok(Box::new(PointerType {
            span: indirection.span.clone(),
            inner,
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::assert_ok;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::syntax::Type;

    fn assert_parse<T>(input: &str, rule: impl FnOnce(&mut Parser) -> T) -> T {
        let mut p = Parser::new(Lexer::new(input));
        let production = rule(&mut p);
        let next = assert_ok!(p.peek_token());
        if let Some(next) = next {
            assert!(false, "expected end of stream, got {:?}", next);
        }
        production
    }

    #[test]
    fn test_parse_builtin_type() {
        let prod = assert_parse("i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Integer32(_)));

        let prod = assert_parse("void", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Unit(_)));
    }

    #[test]
    fn test_parse_named_type() {
        let prod = assert_parse("Matrix", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Named(inner) if inner.name.name == "Matrix"));
    }

    #[test]
    fn test_parse_pointer_type() {
        let prod = assert_parse("*i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Pointer(_)));
        if let Type::Pointer(ptr) = *prod {
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, Type::Integer32(_)));
        }

        let prod = assert_parse("**i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Pointer(_)));
        if let Type::Pointer(ptr) = *prod {
            assert!(matches!(*ptr.inner.as_ref(), Type::Pointer(_)));
            let inner = ptr.inner.as_ref();
            if let Type::Pointer(ptr) = inner {
                let inner = ptr.inner.as_ref();
                assert!(matches!(inner, Type::Integer32(_)));
            }
        }

        let prod = assert_parse("*vec2", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Type::Pointer(_)));
        if let Type::Pointer(ptr) = *prod {
            assert!(matches!(*ptr.inner.as_ref(), Type::Named(_)));
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, Type::Named(name) if name.name.name == "vec2"));
        }
    }
}
