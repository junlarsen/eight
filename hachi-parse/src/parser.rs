use crate::ast::{
    Expr, FunctionItem, FunctionParameterItem, Identifier, Integer32Type, Item, LetStmt, NamedType,
    PointerType, Stmt, TranslationUnit, Type, TypeItem, TypeMemberItem, UnitType,
};
use crate::lexer::{Lexer, LexerError, LexerIter};
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

    /// Parse a translation unit.
    ///
    /// ```text
    /// translation_unit ::= item*
    /// ```
    pub fn parse_translation_unit(&mut self) -> ParseResult<Box<TranslationUnit>> {
        let mut items = Vec::new();
        while self.has_next_token() {
            items.push(self.parse_item()?);
        }
        Ok(Box::new(TranslationUnit { items }))
    }

    /// Parse an item.
    ///
    /// ```text
    /// item ::= fn_item | type_item
    /// ```
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

    /// Parse a function item.
    ///
    /// ```text
    /// fn_item ::= KEYWORD_FN IDENTIFIER OPEN_PAREN
    ///             ((fn_parameter_item COMMA)+ fn_parameter_item)?
    ///             CLOSE_PAREN (ARROW type)? OPEN_BRACE stmt* CLOSE_BRACE
    /// ```
    pub fn parse_fn_item(&mut self) -> ParseResult<Box<FunctionItem>> {
        self.expect_token(TokenType::KeywordFn)?;
        let id = self.parse_identifier()?;
        self.expect_token(TokenType::OpenParen)?;
        let mut parameters = Vec::new();
        while !self.peek_token_match(TokenType::CloseParen)? {
            let parameter = self.parse_fn_parameter_item()?;
            // Consume commas if we're not matching the end of the parameter list.
            if !self.peek_token_match(TokenType::CloseParen)? {
                self.expect_token(TokenType::Comma)?;
            }
            parameters.push(parameter);
        }
        self.expect_token(TokenType::CloseParen)?;
        let return_type = if self.peek_token_match(TokenType::Arrow)? {
            self.expect_token(TokenType::Arrow)?;
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect_token(TokenType::OpenBrace)?;
        self.expect_token(TokenType::CloseBrace)?;

        Ok(Box::new(FunctionItem {
            span: id.span.clone(),
            name: id,
            parameters,
            return_type,
            body: Vec::new(),
        }))
    }

    /// Parse a function parameter item.
    ///
    /// ```text
    /// fn_parameter_item ::= identifier COLON type
    /// ```
    pub fn parse_fn_parameter_item(&mut self) -> ParseResult<Box<FunctionParameterItem>> {
        let id = self.parse_identifier()?;
        self.expect_token(TokenType::Colon)?;
        let ty = self.parse_type()?;
        Ok(Box::new(FunctionParameterItem {
            span: id.span.clone(),
            name: id,
            r#type: ty,
        }))
    }

    /// Parse a type item.
    ///
    /// ```text
    /// type_item ::= KEYWORD_TYPE identifier EQUAL OPEN_BRACE type_member_item* CLOSE_BRACE
    /// ```
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

    /// Parse a type member item.
    ///
    /// ```text
    /// type_member_item ::= identifier COLON type COMMA
    /// ```
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

    /// Parse a statement.
    ///
    /// ```text
    /// stmt ::= let_stmt
    ///        | return_stmt
    ///        | for_stmt
    ///        | break_stmt
    ///        | continue_stmt
    ///        | if_stmt
    ///        | expr_stmt
    /// ```
    pub fn parse_stmt(&mut self) -> ParseResult<Box<Stmt>> {
        let next = self.peek_token()?.ok_or(ParseError::UnexpectedEndOfFile)?;
    }

    /// Parse a let statement.
    ///
    /// ```text
    /// let_stmt ::= KEYWORD_LET IDENTIFIER (COLON type)? EQUAL expr SEMICOLON
    /// ```
    pub fn parse_let_stmt(&mut self) -> ParseResult<Box<LetStmt>> {
        self.expect_token(TokenType::KeywordLet)?;
        let id = self.parse_identifier()?;
        let ty = if self.peek_token_match(TokenType::Colon) {
            self.expect_token(TokenType::Colon)?;
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect_token(TokenType::Equal)?;
        let expr = self.parse_expr()?;
        self.expect_token(TokenType::Semicolon)?;

        Ok(Box::new(LetStmt {
            span: id.span.clone(),
            name: id,
            r#type: ty,
            value: expr,
        }))
    }

    /// Parse an expression
    ///
    /// ```text
    /// ```
    pub fn parse_expr(&mut self) -> ParseResult<Box<Expr>> {
        todo!()
    }

    /// Parse an identifier.
    ///
    /// ```text
    /// identifier ::= IDENTIFIER
    /// ```
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

    /// Parse a type.
    ///
    /// ```text
    /// type ::= named_type | pointer_type | builtin_void_type | builtin_integer32_type
    ///
    /// builtin_void_type ::= identifier<"void">
    /// builtin_integer32_type ::= identifier<"i32">
    /// ```
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

    /// Parse a named type.
    ///
    /// ```text
    /// named_type ::= identifier
    /// ```
    pub fn parse_named_type(&mut self) -> ParseResult<Box<NamedType>> {
        let id = self.parse_identifier()?;
        Ok(Box::new(NamedType {
            span: id.span.clone(),
            name: id,
        }))
    }

    /// Parse a pointer type of single indirection.
    ///
    /// ```text
    /// pointer_type ::= STAR type
    /// ```
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
    use crate::ast::{Identifier, Type};
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::{assert_none, assert_ok, assert_some};

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

    #[test]
    fn test_parse_type_member_item() {
        let prod = assert_parse("x: i32,", |p| p.parse_type_member_item());
        let prod = assert_ok!(prod);
        let name = prod.name.as_ref();
        let r#type = prod.r#type.as_ref();

        assert!(matches!(name, Identifier { name, .. } if name == "x"));
        assert!(matches!(*r#type, Type::Integer32(_)));

        let prod = assert_parse("x: *matrix,", |p| p.parse_type_member_item());
        let prod = assert_ok!(prod);
        let name = prod.name.as_ref();
        let r#type = prod.r#type.as_ref();

        assert!(matches!(name, Identifier { name, .. } if name == "x"));
        assert!(matches!(*r#type, Type::Pointer(_)));
        if let Type::Pointer(ptr) = &*r#type {
            assert!(matches!(*ptr.inner.as_ref(), Type::Named(_)));
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, Type::Named(name) if name.name.name == "matrix"));
        }
    }

    #[test]
    fn test_parse_type_item() {
        let prod = assert_parse("type Matrix = { x: i32, y: i32, }", |p| p.parse_type_item());
        let prod = assert_ok!(prod);
        let name = prod.name.as_ref();
        let members = prod.members.as_slice();

        assert!(matches!(name, Identifier { name, .. } if name == "Matrix"));
        assert_eq!(members.len(), 2);

        let prod = assert_parse("type Matrix = { x: i32, y: i32, z: *vec2, }", |p| {
            p.parse_type_item()
        });
        let prod = assert_ok!(prod);
        let name = prod.name.as_ref();
        let members = prod.members.as_slice();

        assert!(matches!(name, Identifier { name, .. } if name == "Matrix"));
        assert_eq!(members.len(), 3);
    }

    #[test]
    fn test_parse_fn_parameter_item() {
        let prod = assert_parse("x: i32", |p| p.parse_fn_parameter_item());
        let prod = assert_ok!(prod);

        let name = prod.name.as_ref();
        let r#type = prod.r#type.as_ref();

        assert!(matches!(name, Identifier { name, .. } if name == "x"));
        assert!(matches!(*r#type, Type::Integer32(_)));
    }

    #[test]
    fn test_parse_fn_item() {
        let prod = assert_parse("fn x(y: i32) -> i32 {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let name = prod.name.as_ref();
        let parameters = prod.parameters.as_slice();
        let return_type = assert_some!(prod.return_type);
        let body = prod.body.as_slice();

        assert!(matches!(name, Identifier { name, .. } if name == "x"));
        assert_eq!(parameters.len(), 1);
        assert!(matches!(*return_type, Type::Integer32(_)));
        assert_eq!(body.len(), 0);

        let prod = assert_parse("fn zzz(y: *i32) {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let name = prod.name.as_ref();
        let parameters = prod.parameters.as_slice();
        assert_none!(prod.return_type.as_ref());
        let body = prod.body.as_slice();

        assert!(matches!(name, Identifier { name, .. } if name == "zzz"));
        assert_eq!(parameters.len(), 1);
        assert_eq!(body.len(), 0);

        let prod = assert_parse("fn v(x: i32, y: i32) {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let parameters = prod.parameters.as_slice();
        assert_eq!(parameters.len(), 2);

        let prod = assert_parse("fn foo() {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let parameters = prod.parameters.as_slice();
        assert_eq!(parameters.len(), 0);
    }
}
