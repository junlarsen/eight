use crate::arena::AstArena;
use crate::ast::{
    AstAssignExpr, AstBinaryOp, AstBinaryOpExpr, AstBooleanLiteralExpr, AstBooleanType,
    AstBracketIndexExpr, AstBreakStmt, AstCallExpr, AstConstructExpr, AstConstructorExprArgument,
    AstContinueStmt, AstDotIndexExpr, AstExpr, AstExprStmt, AstForStmt, AstForStmtInitializer,
    AstFunctionItem, AstFunctionParameterItem, AstGroupExpr, AstIdentifier, AstIfStmt,
    AstInstanceItem, AstInteger32Type, AstIntegerLiteralExpr, AstIntrinsicFunctionItem,
    AstIntrinsicTypeItem, AstItem, AstLetStmt, AstNamedType, AstPointerType, AstReferenceExpr,
    AstReturnStmt, AstStmt, AstStructItem, AstStructMemberItem, AstTraitFunctionItem, AstTraitItem,
    AstTranslationUnit, AstType, AstTypeParameterItem, AstUnaryOp, AstUnaryOpExpr, AstUnitType,
};
use crate::error::{ParseError, ParseResult, UnexpectedEndOfFileError, UnexpectedTokenError};
use crate::lexer::Lexer;
use crate::tok::{Token, TokenType};
use eight_span::Span;

pub struct ParserInput<'a> {
    lexer: &'a mut Lexer<'a>,
    /// Buffer for the next token lookahead.
    ///
    /// If the parser for any reason needs more than LL(1) in the future, this can be replaced with
    /// a stack of tokens.
    la: Option<Token>,
}

impl<'a> ParserInput<'a> {
    pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
        Self { lexer, la: None }
    }

    /// Perform a single token lookahead.
    ///
    /// This function will fail the entire parser if the lexer fails to produce a token, except when
    /// the lexer reaches the end of input.
    pub fn lookahead(&mut self) -> ParseResult<Option<&Token>> {
        if self.la.is_none() {
            self.la = loop {
                match self.lexer.produce() {
                    Ok(tok) if matches!(tok.ty, TokenType::Comment(_)) => continue,
                    Ok(tok) => break Some(tok),
                    Err(ParseError::UnexpectedEndOfFile(_)) => break None,
                    Err(err) => return Err(err),
                }
            };
        }
        Ok(self.la.as_ref())
    }

    /// Consume the next token from the token stream.
    ///
    /// This does not optimistically peek at the next token. As with the `lookahead` function, this
    /// function will fail the entire parser if the lexer fails.
    pub fn eat(&mut self) -> ParseResult<Token> {
        if let Some(token) = self.la.take() {
            return Ok(token);
        }
        loop {
            match self.lexer.produce() {
                Ok(tok) if matches!(tok.ty, TokenType::Comment(_)) => continue,
                e => break e,
            }
        }
    }
}

pub struct Parser<'a, 'ast> {
    input: ParserInput<'a>,
    arena: &'ast AstArena<'ast>,
}

impl<'a, 'ast> Parser<'a, 'ast> {
    /// Create a new parser from a given lexer.
    ///
    /// The current grammar will make consume the entire lexer, but in the future, we may support
    /// partial parsing, so taking ownership of the lexer is not a requirement.
    pub fn new(lexer: &'a mut Lexer<'a>, arena: &'ast AstArena<'ast>) -> Self {
        Self {
            input: ParserInput::new(lexer),
            arena,
        }
    }

    /// Advance the lexer iterator by one, and return the advanced token.
    pub fn eat(&mut self) -> ParseResult<Token> {
        self.input.eat()
    }

    /// Peek at the next token in the source without consuming it.
    ///
    /// If the lexer fails here, we're just going to silently ignore it and return `None`.
    pub fn lookahead(&mut self) -> ParseResult<Option<&Token>> {
        let tok = self.input.lookahead()?;
        if let Some(token) = tok {
            return Ok(Some(token));
        }
        Ok(None)
    }

    /// Peek at the next token in the source without consuming it.
    ///
    /// As indicated by the name, this function fails the parser if the lexer cannot produce a
    /// next token.
    pub fn lookahead_or_err(&mut self) -> ParseResult<&Token> {
        let pos = self.input.lexer.pos();
        self.input
            .lookahead()?
            .ok_or(ParseError::UnexpectedEndOfFile(UnexpectedEndOfFileError {
                span: Span::new(pos..pos),
            }))
    }

    /// Determine if the next token in the token stream matches the given type.
    pub fn lookahead_check(&mut self, ty: &TokenType) -> ParseResult<bool> {
        let token = self.lookahead()?;
        match token {
            Some(token) if token.ty == *ty => Ok(true),
            _ => Ok(false),
        }
    }

    /// Consume the next token from the token stream and ensure it matches the given type.
    ///
    /// If the token doesn't match, the entire parser fails.
    pub fn check(&mut self, ty: &TokenType) -> ParseResult<Token> {
        let token = self.eat()?;
        match token {
            token if token.ty == *ty => Ok(token),
            _ => Err(ParseError::UnexpectedToken(UnexpectedTokenError {
                span: token.span,
                token,
            })),
        }
    }

    /// Apply the given parser `f` to the parser repeatedly until the next token matches the given
    /// circuit breaker.
    ///
    /// Parses the applied parser `f` until the next token matches the given circuit breaker, with
    /// each call to `f` being interleaved by a single consumption of the delimiter token.
    ///
    /// This function does not consume the circuit breaker token.
    pub fn parser_combinator_delimited<'p, T, F>(
        &mut self,
        delimiter: &TokenType,
        circuit_breaker: &TokenType,
        f: F,
    ) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Parser<'a, 'ast>) -> ParseResult<T>,
    {
        let mut items = Vec::new();
        while !self.lookahead_check(circuit_breaker)? {
            items.push(f(self)?);
            if !self.lookahead_check(circuit_breaker)? {
                self.check(delimiter)?;
            }
        }
        Ok(items)
    }

    /// Optionally apply `f`, decided by the `decision_maker` token.
    ///
    /// If the decision maker token is matched, the parser `f` is applied to the parser and the
    /// result is wrapped in `Some`. Otherwise, the result is `None`.
    ///
    /// The combinator consumes the decision maker token before applying `f`.
    pub fn parser_combinator_take_if<T, F, M>(&mut self, matcher: M, f: F) -> ParseResult<Option<T>>
    where
        F: FnOnce(&mut Parser<'a, 'ast>) -> ParseResult<T>,
        M: FnOnce(&Token) -> bool,
    {
        let token = self.lookahead()?;
        match token {
            Some(token) if matcher(token) => Ok(Some(f(self)?)),
            _ => Ok(None),
        }
    }

    /// Apply the given parser `f` to the parser repeatedly until the next token matches the given
    /// circuit breaker.
    ///
    /// This function does not consume the circuit breaker token.
    pub fn parser_combinator_many<T, F>(
        &mut self,
        circuit_breaker: &TokenType,
        f: F,
    ) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Parser<'a, 'ast>) -> ParseResult<T>,
    {
        let mut items = Vec::new();
        while !self.lookahead_check(circuit_breaker)? {
            items.push(f(self)?);
        }
        Ok(items)
    }
}

impl<'a, 'ast> Parser<'a, 'ast> {
    /// Top-level entry for parsing a translation unit (file).
    pub fn parse(&mut self) -> ParseResult<AstTranslationUnit<'ast>> {
        self.parse_translation_unit()
    }

    /// Parse a translation unit.
    ///
    /// ```text
    /// translation_unit ::= item*
    /// ```
    pub fn parse_translation_unit(&mut self) -> ParseResult<AstTranslationUnit<'ast>> {
        let mut items = Vec::new();
        while self.lookahead()?.is_some() {
            items.push(self.parse_item()?);
        }
        // The translation unit doesn't record a span
        let node = AstTranslationUnit {
            items: self.arena.alloc_vec(items),
        };
        Ok(node)
    }

    /// Parse an item.
    ///
    /// ```text
    /// item ::= fn_item | struct_item | intrinsic_fn_item | trait_item | instance_item
    /// ```
    pub fn parse_item(&mut self) -> ParseResult<AstItem<'ast>> {
        let token = self.lookahead_or_err()?;
        let node = match token.ty {
            TokenType::KeywordFn => AstItem::Function(self.parse_fn_item()?),
            TokenType::KeywordStruct => AstItem::Struct(self.parse_struct_item()?),
            TokenType::KeywordIntrinsicFn => {
                AstItem::IntrinsicFunction(self.parse_intrinsic_fn_item()?)
            }
            TokenType::KeywordIntrinsicType => {
                AstItem::IntrinsicType(self.parse_intrinsic_type_item()?)
            }
            TokenType::KeywordTrait => AstItem::Trait(self.parse_trait_item()?),
            TokenType::KeywordInstance => AstItem::Instance(self.parse_instance_item()?),
            _ => {
                let token = self.eat()?;
                return Err(ParseError::UnexpectedToken(UnexpectedTokenError {
                    span: token.span,
                    token,
                }));
            }
        };
        Ok(node)
    }

    /// Parse a function item.
    ///
    /// ```text
    /// fn_item ::= KEYWORD_FN IDENTIFIER
    ///             (OPEN_ANGLE ((type_parameter_item COMMA)+ type_parameter_item)? CLOSE_ANGLE)?
    ///             OPEN_PAREN ((fn_parameter_item COMMA)+ fn_parameter_item)? CLOSE_PAREN
    ///             CLOSE_PAREN (ARROW type)? OPEN_BRACE stmt* CLOSE_BRACE
    /// ```
    pub fn parse_fn_item(&mut self) -> ParseResult<AstFunctionItem<'ast>> {
        let start = self.check(&TokenType::KeywordFn)?;
        let id = self.parse_identifier()?;
        let type_parameters = self
            .parser_combinator_take_if(
                |t| t.ty == TokenType::OpenAngle,
                |p| {
                    p.check(&TokenType::OpenAngle)?;
                    let type_parameters = p.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseAngle,
                        |p| p.parse_type_parameter_item(),
                    )?;
                    p.check(&TokenType::CloseAngle)?;
                    Ok(type_parameters)
                },
            )?
            .unwrap_or(vec![]);
        // Parse the function's parameter list
        self.check(&TokenType::OpenParen)?;
        let parameters =
            self.parser_combinator_delimited(&TokenType::Comma, &TokenType::CloseParen, |p| {
                p.parse_fn_parameter_item()
            })?;
        self.check(&TokenType::CloseParen)?;
        // Optionally take a return type if it's specified
        let return_type = self.parser_combinator_take_if(
            |t| t.ty == TokenType::Arrow,
            |p| {
                p.check(&TokenType::Arrow)?;
                p.parse_type()
            },
        )?;
        // Parse the function's body
        self.check(&TokenType::OpenBrace)?;
        let body = self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_stmt())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstFunctionItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            parameters: self.arena.alloc_ref_vec(parameters),
            type_parameters: self.arena.alloc_ref_vec(type_parameters),
            return_type: return_type.map(|t| &*self.arena.alloc(t)),
            body: self.arena.alloc_vec(body),
        };
        Ok(node)
    }

    /// Parse a function parameter item.
    ///
    /// ```text
    /// fn_parameter_item ::= identifier COLON type
    /// ```
    pub fn parse_fn_parameter_item(&mut self) -> ParseResult<&'ast AstFunctionParameterItem<'ast>> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let ty = self.parse_type()?;
        let node = AstFunctionParameterItem {
            span: Span::from_pair(&id.span, ty.span()),
            name: self.arena.alloc(id),
            ty: self.arena.alloc(ty),
        };
        Ok(self.arena.alloc(node))
    }

    /// Parse a function type parameter item.
    ///
    /// ```text
    /// type_parameter_item ::= identifier
    /// ```
    pub fn parse_type_parameter_item(&mut self) -> ParseResult<&'ast AstTypeParameterItem<'ast>> {
        let id = self.parse_identifier()?;
        let node = AstTypeParameterItem {
            span: id.span,
            name: self.arena.alloc(id),
        };
        Ok(self.arena.alloc(node))
    }

    /// Parse a struct item.
    ///
    /// ```text
    /// struct_item ::= KEYWORD_STRUCT identifier OPEN_BRACE type_member_item* CLOSE_BRACE
    /// ```
    pub fn parse_struct_item(&mut self) -> ParseResult<AstStructItem<'ast>> {
        let start = self.check(&TokenType::KeywordStruct)?;
        let id = self.parse_identifier()?;
        self.check(&TokenType::OpenBrace)?;
        let members =
            self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_type_member_item())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstStructItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            members: self.arena.alloc_vec(members),
        };
        Ok(node)
    }

    /// Parse a struct member item.
    ///
    /// ```text
    /// struct_member_item ::= identifier COLON type COMMA
    /// ```
    pub fn parse_type_member_item(&mut self) -> ParseResult<AstStructMemberItem<'ast>> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let ty = self.parse_type()?;
        let end = self.check(&TokenType::Comma)?;
        let node = AstStructMemberItem {
            span: Span::from_pair(&id.span, &end.span),
            name: self.arena.alloc(id),
            ty: self.arena.alloc(ty),
        };
        Ok(node)
    }

    /// Parse an intrinsic function item.
    ///
    /// Unlike regular functions, intrinsic functions must have their return type specified.
    ///
    /// ```text
    /// intrinsic_fn_item ::= KEYWORD_INTRINSIC_FN IDENTIFIER
    ///                       (OPEN_ANGLE ((type_parameter_item COMMA)+ type_parameter_item)? CLOSE_ANGLE)?
    ///                       OPEN_PAREN ((fn_parameter_item COMMA)+ fn_parameter_item)? CLOSE_PAREN
    ///                       ARROW type SEMICOLON
    /// ```
    pub fn parse_intrinsic_fn_item(&mut self) -> ParseResult<AstIntrinsicFunctionItem<'ast>> {
        let start = self.check(&TokenType::KeywordIntrinsicFn)?;
        let id = self.parse_identifier()?;
        let type_parameters = self
            .parser_combinator_take_if(
                |t| t.ty == TokenType::OpenAngle,
                |p| {
                    p.check(&TokenType::OpenAngle)?;
                    let type_parameters = p.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseAngle,
                        |p| p.parse_type_parameter_item(),
                    )?;
                    p.check(&TokenType::CloseAngle)?;
                    Ok(type_parameters)
                },
            )?
            .unwrap_or(vec![]);
        self.check(&TokenType::OpenParen)?;
        let parameters =
            self.parser_combinator_delimited(&TokenType::Comma, &TokenType::CloseParen, |p| {
                p.parse_fn_parameter_item()
            })?;
        self.check(&TokenType::CloseParen)?;
        self.check(&TokenType::Arrow)?;
        let return_type = self.parse_type()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstIntrinsicFunctionItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            parameters: self.arena.alloc_ref_vec(parameters),
            type_parameters: self.arena.alloc_ref_vec(type_parameters),
            return_type: self.arena.alloc(return_type),
        };
        Ok(node)
    }

    /// Parse an intrinsic type item.
    ///
    /// ```text
    /// intrinsic_type_item ::= KEYWORD_INTRINSIC_FN IDENTIFIER SEMICOLON
    /// ```
    pub fn parse_intrinsic_type_item(&mut self) -> ParseResult<AstIntrinsicTypeItem<'ast>> {
        let start = self.check(&TokenType::KeywordIntrinsicType)?;
        let id = self.parse_identifier()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstIntrinsicTypeItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
        };
        Ok(node)
    }

    /// Parse a trait item.
    ///
    /// At the moment, we require at least one type parameter on the trait. Otherwise, it would not
    /// make sense to have an instance of it.
    ///
    /// TODO: Consider if we should change syntax to `instance Trait for Type` syntax instead.
    ///
    /// ```text
    /// trait_item ::= KEYWORD_TRAIT IDENTIFIER
    ///                OPEN_ANGLE ((type_parameter_item COMMA)+ type_parameter_item) CLOSE_ANGLE
    ///                OPEN_BRACE trait_function_item* CLOSE_BRACE
    ///
    pub fn parse_trait_item(&mut self) -> ParseResult<AstTraitItem<'ast>> {
        let start = self.check(&TokenType::KeywordTrait)?;
        let id = self.parse_identifier()?;
        let type_parameters = self
            .parser_combinator_take_if(
                |t| t.ty == TokenType::OpenAngle,
                |p| {
                    p.check(&TokenType::OpenAngle)?;
                    let type_parameters = p.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseAngle,
                        |p| p.parse_type_parameter_item(),
                    )?;
                    p.check(&TokenType::CloseAngle)?;
                    Ok(type_parameters)
                },
            )?
            .unwrap_or(vec![]);
        self.check(&TokenType::OpenBrace)?;
        let members =
            self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_trait_function_item())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstTraitItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            type_parameters: self.arena.alloc_ref_vec(type_parameters),
            members: self.arena.alloc_vec(members),
        };
        Ok(node)
    }

    /// Parse a trait function item.
    ///
    /// ```text
    /// trait_function_item ::= KEYWORD_FN IDENTIFIER
    ///                         (OPEN_ANGLE ((type_parameter_item COMMA)+ type_parameter_item)? CLOSE_ANGLE)?
    ///                         OPEN_PAREN ((fn_parameter_item COMMA)+ fn_parameter_item)? CLOSE_PAREN
    ///                         (ARROW type)? SEMICOLON
    pub fn parse_trait_function_item(&mut self) -> ParseResult<AstTraitFunctionItem<'ast>> {
        let start = self.check(&TokenType::KeywordFn)?;
        let id = self.parse_identifier()?;
        let type_parameters = self
            .parser_combinator_take_if(
                |t| t.ty == TokenType::OpenAngle,
                |p| {
                    p.check(&TokenType::OpenAngle)?;
                    let type_parameters = p.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseAngle,
                        |p| p.parse_type_parameter_item(),
                    )?;
                    p.check(&TokenType::CloseAngle)?;
                    Ok(type_parameters)
                },
            )?
            .unwrap_or(vec![]);
        self.check(&TokenType::OpenParen)?;
        let parameters =
            self.parser_combinator_delimited(&TokenType::Comma, &TokenType::CloseParen, |p| {
                p.parse_fn_parameter_item()
            })?;
        self.check(&TokenType::CloseParen)?;
        let return_type = self.parser_combinator_take_if(
            |t| t.ty == TokenType::Arrow,
            |p| {
                p.check(&TokenType::Arrow)?;
                p.parse_type()
            },
        )?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstTraitFunctionItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            type_parameters: self.arena.alloc_ref_vec(type_parameters),
            parameters: self.arena.alloc_ref_vec(parameters),
            return_type: return_type.map(|t| &*self.arena.alloc(t)),
        };
        Ok(node)
    }

    /// Parse an instance item.
    ///
    /// ```text
    /// instance_item ::= KEYWORD_INSTANCE IDENTIFIER
    ///                   OPEN_ANGLE ((type (COMMA type)*)? CLOSE_ANGLE)?
    ///                   OPEN_BRACE fn_item* CLOSE_BRACE
    /// ```
    pub fn parse_instance_item(&mut self) -> ParseResult<AstInstanceItem<'ast>> {
        let start = self.check(&TokenType::KeywordInstance)?;
        let id = self.parse_identifier()?;
        let instantiation_type_parameters = self
            .parser_combinator_take_if(
                |t| t.ty == TokenType::OpenAngle,
                |p| {
                    p.check(&TokenType::OpenAngle)?;
                    let type_parameters = p.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseAngle,
                        |p| p.parse_type(),
                    )?;
                    p.check(&TokenType::CloseAngle)?;
                    Ok(type_parameters)
                },
            )?
            .unwrap_or(vec![]);
        self.check(&TokenType::OpenBrace)?;
        let members = self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_fn_item())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstInstanceItem {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            instantiation_type_parameters: self.arena.alloc_vec(instantiation_type_parameters),
            members: self.arena.alloc_vec(members),
        };
        Ok(node)
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
    pub fn parse_stmt(&mut self) -> ParseResult<AstStmt<'ast>> {
        let next = self.lookahead_or_err()?;
        let node = match next.ty {
            TokenType::KeywordLet => AstStmt::Let(self.parse_let_stmt()?),
            TokenType::KeywordReturn => AstStmt::Return(self.parse_return_stmt()?),
            TokenType::KeywordFor => AstStmt::For(self.parse_for_stmt()?),
            TokenType::KeywordBreak => AstStmt::Break(self.parse_break_stmt()?),
            TokenType::KeywordContinue => AstStmt::Continue(self.parse_continue_stmt()?),
            TokenType::KeywordIf => AstStmt::If(self.parse_if_stmt()?),
            _ => AstStmt::Expr(self.parse_expr_stmt()?),
        };
        Ok(node)
    }

    /// Parse a let statement.
    ///
    /// ```text
    /// let_stmt ::= KEYWORD_LET IDENTIFIER (COLON type)? EQUAL expr SEMICOLON
    /// ```
    pub fn parse_let_stmt(&mut self) -> ParseResult<AstLetStmt<'ast>> {
        let start = self.check(&TokenType::KeywordLet)?;
        let id = self.parse_identifier()?;
        let ty = self.parser_combinator_take_if(
            |t| t.ty == TokenType::Colon,
            |p| {
                p.check(&TokenType::Colon)?;
                p.parse_type()
            },
        )?;
        self.check(&TokenType::Equal)?;
        let expr = self.parse_expr()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstLetStmt {
            span: Span::from_pair(&start.span, &end.span),
            name: self.arena.alloc(id),
            ty: ty.map(|t| &*self.arena.alloc(t)),
            value: self.arena.alloc(expr),
        };
        Ok(node)
    }

    /// Parses a return statement.
    ///
    /// ```text
    /// return_stmt ::= RETURN expr? SEMICOLON
    /// ```
    pub fn parse_return_stmt(&mut self) -> ParseResult<AstReturnStmt<'ast>> {
        let start = self.check(&TokenType::KeywordReturn)?;
        let value =
            self.parser_combinator_take_if(|t| t.ty != TokenType::Semicolon, |p| p.parse_expr())?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstReturnStmt {
            span: Span::from_pair(&start.span, &end.span),
            value: value.map(|v| &*self.arena.alloc(v)),
        };
        Ok(node)
    }

    /// Parses a for statement.
    ///
    /// ```text
    /// for_stmt ::= FOR LPAREN for_stmt_initializer? SEMICOLON expr? SEMICOLON expr? RPAREN LBRACE stmt* RBRACE
    /// ```
    pub fn parse_for_stmt(&mut self) -> ParseResult<AstForStmt<'ast>> {
        let start = self.check(&TokenType::KeywordFor)?;
        self.check(&TokenType::OpenParen)?;
        let initializer = self.parser_combinator_take_if(
            |t| t.ty != TokenType::Semicolon,
            |p| p.parse_for_stmt_initializer(),
        )?;
        self.check(&TokenType::Semicolon)?;
        let condition =
            self.parser_combinator_take_if(|t| t.ty != TokenType::Semicolon, |p| p.parse_expr())?;
        self.check(&TokenType::Semicolon)?;
        let increment =
            self.parser_combinator_take_if(|t| t.ty != TokenType::CloseParen, |p| p.parse_expr())?;
        self.check(&TokenType::CloseParen)?;
        self.check(&TokenType::OpenBrace)?;
        let body = self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_stmt())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstForStmt {
            span: Span::from_pair(&start.span, &end.span),
            initializer: initializer.map(|i| &*self.arena.alloc(i)),
            condition: condition.map(|c| &*self.arena.alloc(c)),
            increment: increment.map(|i| &*self.arena.alloc(i)),
            body: self.arena.alloc_vec(body),
        };
        Ok(node)
    }

    /// Parses a for statement initializer.
    ///
    /// ```text
    /// for_stmt_initializer ::= LET identifier EQUAL expr
    /// ```
    pub fn parse_for_stmt_initializer(&mut self) -> ParseResult<AstForStmtInitializer<'ast>> {
        let start = self.check(&TokenType::KeywordLet)?;
        let name = self.parse_identifier()?;
        self.check(&TokenType::Equal)?;
        let initializer = self.parse_expr()?;
        let node = AstForStmtInitializer {
            span: Span::from_pair(&start.span, initializer.span()),
            name: self.arena.alloc(name),
            initializer: self.arena.alloc(initializer),
        };
        Ok(node)
    }

    /// Parses a break statement.
    ///
    /// ```text
    /// break_stmt ::= BREAK SEMICOLON
    /// ```
    pub fn parse_break_stmt(&mut self) -> ParseResult<AstBreakStmt> {
        let start = self.check(&TokenType::KeywordBreak)?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstBreakStmt {
            span: Span::from_pair(&start.span, &end.span),
        };
        Ok(node)
    }

    /// Parses a continue statement.
    ///
    /// ```text
    /// continue_stmt ::= CONTINUE SEMICOLON
    /// ```
    pub fn parse_continue_stmt(&mut self) -> ParseResult<AstContinueStmt> {
        let start = self.check(&TokenType::KeywordContinue)?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstContinueStmt {
            span: Span::from_pair(&start.span, &end.span),
        };
        Ok(node)
    }

    /// Parses an if statement.
    ///
    /// ```text
    /// if_stmt ::= IF LPAREN expr RPAREN LBRACE stmt* RBRACE (ELSE LBRACE stmt* RBRACE)?
    pub fn parse_if_stmt(&mut self) -> ParseResult<AstIfStmt<'ast>> {
        let start = self.check(&TokenType::KeywordIf)?;
        self.check(&TokenType::OpenParen)?;
        let condition = self.parse_expr()?;
        self.check(&TokenType::CloseParen)?;
        self.check(&TokenType::OpenBrace)?;
        let body = self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_stmt())?;
        let mut end = self.check(&TokenType::CloseBrace)?;
        // We default to the end of the if statement by its closing brace if it doesn't have an else
        // block attached. Otherwise, we use the end of the else block.
        let r#else = self.parser_combinator_take_if(
            |t| t.ty == TokenType::KeywordElse,
            |p| {
                p.check(&TokenType::KeywordElse)?;
                p.check(&TokenType::OpenBrace)?;
                let r#else =
                    p.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_stmt())?;
                end = p.check(&TokenType::CloseBrace)?;
                Ok(r#else)
            },
        )?;
        let node = AstIfStmt {
            span: Span::from_pair(&start.span, &end.span),
            condition: self.arena.alloc(condition),
            happy_path: self.arena.alloc_vec(body),
            unhappy_path: r#else.map(|e| self.arena.alloc_vec(e)),
        };
        Ok(node)
    }

    /// Parses an expression statement.
    ///
    /// ```text
    /// expr_stmt ::= expr SEMICOLON
    pub fn parse_expr_stmt(&mut self) -> ParseResult<AstExprStmt<'ast>> {
        let expr = self.parse_expr()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstExprStmt {
            span: Span::from_pair(expr.span(), &end.span),
            expr: self.arena.alloc(expr),
        };
        Ok(node)
    }

    /// Parse an expression
    ///
    /// ```text
    /// expr ::=
    /// ```
    ///
    /// Parsing of expressions is implemented using a climbing algorithm as described in this
    /// [Wikipedia article][precedence_climber].
    ///
    /// The order of operator precedence is as follows:
    ///
    /// 1. Group Expression
    /// 2. Literal Expression
    /// 3. Reference Expression
    /// 4. PostFix Expression (BracketIndex, DotIndex, Call)
    /// 5. Construct Expression
    /// 6. Unary Expression
    /// 7. Multiplicative Expression
    /// 8. Additive Expression
    /// 9. Binary Expression
    /// 10. Comparison Expression
    /// 11. Logical And Expression
    /// 12. Logical Or Expression
    /// 13. Assign Expression
    ///
    /// [precedence_climber]: https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
    pub fn parse_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        self.parse_assign_expr()
    }

    /// Parse an assignment expression.
    ///
    /// ```text
    /// assign_expr ::= logical_expr EQUAL assign_expr
    /// ```
    pub fn parse_assign_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let expr = self.parse_logical_or_expr()?;

        if self.lookahead_check(&TokenType::Equal)? {
            self.check(&TokenType::Equal)?;
            let rhs = self.parse_assign_expr()?;
            let node = AstAssignExpr {
                span: Span::from_pair(expr.span(), rhs.span()),
                lhs: self.arena.alloc(expr),
                rhs: self.arena.alloc(rhs),
            };
            return Ok(AstExpr::Assign(node));
        };

        Ok(expr)
    }

    /// Parse a logical or expression.
    ///
    /// ```text
    /// logical_or_expr ::= logical_and_expr (OR logical_and_expr)*
    /// ```
    pub fn parse_logical_or_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let lhs = self.parse_logical_and_expr()?;

        if self.lookahead_check(&TokenType::LogicalOr)? {
            let op_token = self.check(&TokenType::LogicalOr)?;
            let rhs = self.parse_logical_or_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: self.arena.alloc(lhs),
                rhs: self.arena.alloc(rhs),
                op: AstBinaryOp::Or,
                op_span: op_token.span,
            };
            return Ok(AstExpr::BinaryOp(node));
        };

        Ok(lhs)
    }

    /// Parse a logical and expression.
    ///
    /// ```text
    /// logical_and_expr ::= comparison_expr (AND comparison_expr)*
    /// ```
    pub fn parse_logical_and_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let lhs = self.parse_comparison_expr()?;

        if self.lookahead_check(&TokenType::LogicalAnd)? {
            let op_token = self.check(&TokenType::LogicalAnd)?;
            let rhs = self.parse_logical_and_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: self.arena.alloc(lhs),
                rhs: self.arena.alloc(rhs),
                op: AstBinaryOp::And,
                op_span: op_token.span,
            };
            return Ok(AstExpr::BinaryOp(node));
        };

        Ok(lhs)
    }

    /// Parse a comparison expression.
    ///
    /// ```text
    /// comparison_expr ::= additive_expr (comparison_op additive_expr)*
    /// comparison_op ::= EQUAL_EQUAL | BANG_EQUAL | LESS_THAN | GREATER_THAN | LESS_THAN_EQUAL | GREATER_THAN_EQUAL
    /// ```
    pub fn parse_comparison_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let lhs = self.parse_additive_expr()?;
        let is_next_comparison = self.lookahead_check(&TokenType::EqualEqual)?
            || self.lookahead_check(&TokenType::BangEqual)?
            || self.lookahead_check(&TokenType::OpenAngle)?
            || self.lookahead_check(&TokenType::CloseAngle)?
            || self.lookahead_check(&TokenType::LessThanEqual)?
            || self.lookahead_check(&TokenType::GreaterThanEqual)?;

        if is_next_comparison {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::EqualEqual => AstBinaryOp::Eq,
                TokenType::BangEqual => AstBinaryOp::Neq,
                TokenType::OpenAngle => AstBinaryOp::Lt,
                TokenType::CloseAngle => AstBinaryOp::Gt,
                TokenType::LessThanEqual => AstBinaryOp::Lte,
                TokenType::GreaterThanEqual => AstBinaryOp::Gte,
                _ => unreachable!(),
            };
            let rhs = self.parse_comparison_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: self.arena.alloc(lhs),
                rhs: self.arena.alloc(rhs),
                op_span: tok.span,
                op,
            };
            return Ok(AstExpr::BinaryOp(node));
        }

        Ok(lhs)
    }

    /// Parse an additive expression.
    ///
    /// ```text
    /// additive_expr ::= multiplicative_expr (additive_op multiplicative_expr)*
    /// additive_op ::= PLUS | MINUS
    /// ```
    pub fn parse_additive_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let lhs = self.parse_multiplicative_expr()?;
        let is_next_additive =
            self.lookahead_check(&TokenType::Plus)? || self.lookahead_check(&TokenType::Minus)?;

        if is_next_additive {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::Plus => AstBinaryOp::Add,
                TokenType::Minus => AstBinaryOp::Sub,
                _ => unreachable!(),
            };
            let rhs = self.parse_additive_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: self.arena.alloc(lhs),
                rhs: self.arena.alloc(rhs),
                op_span: tok.span,
                op,
            };
            return Ok(AstExpr::BinaryOp(node));
        }

        Ok(lhs)
    }

    /// Parse a multiplicative expression.
    ///
    /// ```text
    /// multiplicative_expr ::= unary_expr (multiplicative_op unary_expr)*
    /// multiplicative_op ::= STAR | SLASH | PERCENT
    /// ```
    pub fn parse_multiplicative_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let lhs = self.parse_unary_expr()?;
        let is_next_multiplicative = self.lookahead_check(&TokenType::Star)?
            || self.lookahead_check(&TokenType::Slash)?
            || self.lookahead_check(&TokenType::Percent)?;

        if is_next_multiplicative {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::Star => AstBinaryOp::Mul,
                TokenType::Slash => AstBinaryOp::Div,
                TokenType::Percent => AstBinaryOp::Rem,
                _ => unreachable!(),
            };
            let rhs = self.parse_multiplicative_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: self.arena.alloc(lhs),
                rhs: self.arena.alloc(rhs),
                op_span: tok.span,
                op,
            };
            return Ok(AstExpr::BinaryOp(node));
        }

        Ok(lhs)
    }

    /// Parse an unary expression.
    ///
    /// ```text
    /// unary_expr ::= unary_op unary_expr | group_expr
    /// unary_op ::= MINUS | BANG | DEREF | STAR
    /// ```
    pub fn parse_unary_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let token = self.lookahead_or_err()?;

        match token.ty {
            TokenType::Minus => {
                let op = self.check(&TokenType::Minus)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: self.arena.alloc(rhs),
                    op: AstUnaryOp::Neg,
                    op_span: op.span,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::Bang => {
                let op = self.check(&TokenType::Bang)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: self.arena.alloc(rhs),
                    op: AstUnaryOp::Not,
                    op_span: op.span,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::Star => {
                let op = self.check(&TokenType::Star)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: self.arena.alloc(rhs),
                    op: AstUnaryOp::Deref,
                    op_span: op.span,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::AddressOf => {
                let op = self.check(&TokenType::AddressOf)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: self.arena.alloc(rhs),
                    op: AstUnaryOp::AddressOf,
                    op_span: op.span,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            _ => self.parse_postfix_expr(),
        }
    }

    /// Parse a postfix expression.
    ///
    /// This ensures that dot index, bracket index, and call expressions all have the same
    /// precedence in the climber.
    ///
    /// ```text
    /// postfix_expr ::= reference_expr
    ///                (
    ///                  | (OPEN_BRACKET expr CLOSE_BRACKET)
    ///                  | (DOT IDENTIFIER)
    ///                  | (COLON_COLON OPEN_ANGLE (type (COMMA type)*)? CLOSE_ANGLE OPEN_PAREN (expr (COMMA expr)*)? CLOSE_PAREN)
    ///                )?
    /// ```
    pub fn parse_postfix_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let mut callee = self.parse_construct_expr()?;
        while let Some(token) = self.lookahead()? {
            match token.ty {
                TokenType::OpenBracket => {
                    self.check(&TokenType::OpenBracket)?;
                    let index = self.parse_expr()?;
                    let end = self.check(&TokenType::CloseBracket)?;
                    let node = AstBracketIndexExpr {
                        span: Span::from_pair(callee.span(), &end.span),
                        origin: self.arena.alloc(callee),
                        index: self.arena.alloc(index),
                    };
                    callee = AstExpr::BracketIndex(node);
                }
                TokenType::Dot => {
                    self.check(&TokenType::Dot)?;
                    let index = self.parse_identifier()?;
                    let node = AstDotIndexExpr {
                        span: Span::from_pair(callee.span(), &index.span),
                        origin: self.arena.alloc(callee),
                        index: self.arena.alloc(index),
                    };
                    callee = AstExpr::DotIndex(node);
                }
                TokenType::ColonColon | TokenType::OpenParen => {
                    let type_arguments = self
                        .parser_combinator_take_if(
                            |t| t.ty == TokenType::ColonColon,
                            |p| {
                                p.check(&TokenType::ColonColon)?;
                                p.check(&TokenType::OpenAngle)?;
                                let arguments = p.parser_combinator_delimited(
                                    &TokenType::Comma,
                                    &TokenType::CloseAngle,
                                    |p| p.parse_type(),
                                )?;
                                p.check(&TokenType::CloseAngle)?;
                                Ok(arguments)
                            },
                        )?
                        .unwrap_or(vec![]);
                    self.check(&TokenType::OpenParen)?;
                    let arguments = self.parser_combinator_delimited(
                        &TokenType::Comma,
                        &TokenType::CloseParen,
                        |p| p.parse_expr(),
                    )?;
                    let end = self.check(&TokenType::CloseParen)?;
                    let node = AstCallExpr {
                        span: Span::from_pair(callee.span(), &end.span),
                        callee: self.arena.alloc(callee),
                        arguments: self.arena.alloc_vec(arguments),
                        type_arguments: self.arena.alloc_vec(type_arguments),
                    };
                    callee = AstExpr::Call(node);
                }
                _ => break,
            }
        }
        Ok(callee)
    }

    /// Parse a construct expression.
    ///
    /// ```text
    /// construct_expr ::= NEW type OPEN_BRACE
    ///                   (construct_expr_argument (COMMA construct_expr_argument)*)?
    ///                   CLOSE_BRACE
    /// ```
    pub fn parse_construct_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        if !self.lookahead_check(&TokenType::KeywordNew)? {
            return self.parse_reference_expr();
        }

        let start = self.check(&TokenType::KeywordNew)?;
        let callee = self.parse_type()?;
        self.check(&TokenType::OpenBrace)?;
        let arguments =
            self.parser_combinator_delimited(&TokenType::Comma, &TokenType::CloseBrace, |p| {
                p.parse_construct_expr_argument()
            })?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstConstructExpr {
            span: Span::from_pair(&start.span, &end.span),
            callee: self.arena.alloc(callee),
            arguments: self.arena.alloc_vec(arguments),
        };
        Ok(AstExpr::Construct(node))
    }

    /// Parse a construct expression argument.
    ///
    /// ```text
    /// construct_expr_argument ::= identifier COLON expr
    pub fn parse_construct_expr_argument(
        &mut self,
    ) -> ParseResult<AstConstructorExprArgument<'ast>> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let expr = self.parse_expr()?;
        let node = AstConstructorExprArgument {
            span: Span::from_pair(&id.span, expr.span()),
            field: self.arena.alloc(id),
            expr: self.arena.alloc(expr),
        };
        Ok(node)
    }

    /// Parse a reference expression.
    ///
    /// ```text
    /// reference_expr ::= identifier | group_expr
    /// ```
    pub fn parse_reference_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        let fut = self.lookahead()?;
        let is_reference = matches!(
            fut,
            Some(Token {
                ty: TokenType::Identifier(_),
                ..
            })
        );
        if is_reference {
            let id = self.parse_identifier()?;
            let node = AstReferenceExpr {
                span: id.span,
                name: self.arena.alloc(id),
            };
            return Ok(AstExpr::Reference(node));
        }
        self.parse_literal_expr()
    }

    /// Parse an integer literal expression.
    ///
    /// ```text
    /// integer_literal_expr ::= INTEGER_LITERAL
    /// ```
    pub fn parse_literal_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        if !self
            .lookahead()?
            .map(|t| t.ty.is_integer_literal() || t.ty.is_boolean_literal())
            .unwrap_or(true)
        {
            return self.parse_group_expr();
        }

        match self.eat()? {
            Token {
                ty: TokenType::IntegerLiteral(v),
                span,
            } => {
                let node = AstIntegerLiteralExpr { span, value: v };
                Ok(AstExpr::IntegerLiteral(node))
            }
            Token {
                ty: TokenType::BooleanLiteral(v),
                span,
            } => {
                let node = AstBooleanLiteralExpr { span, value: v };
                Ok(AstExpr::BooleanLiteral(node))
            }
            _ => self.parse_group_expr(),
        }
    }

    /// Parse a group expression.
    ///
    /// ```text
    /// group_expr ::= OPEN_PAREN expr CLOSE_PAREN
    /// ```
    pub fn parse_group_expr(&mut self) -> ParseResult<AstExpr<'ast>> {
        if self.lookahead_check(&TokenType::OpenParen)? {
            let start = self.check(&TokenType::OpenParen)?;
            let inner = self.parse_expr()?;
            let end = self.check(&TokenType::CloseParen)?;
            let node = AstGroupExpr {
                span: Span::from_pair(&start.span, &end.span),
                inner: self.arena.alloc(inner),
            };
            return Ok(AstExpr::Group(node));
        };
        let token = self.eat()?;
        Err(ParseError::UnexpectedToken(UnexpectedTokenError {
            span: token.span,
            token,
        }))
    }

    /// Parse an identifier.
    ///
    /// ```text
    /// identifier ::= IDENTIFIER
    /// ```
    pub fn parse_identifier(&mut self) -> ParseResult<AstIdentifier> {
        let token = self.eat()?;
        match token {
            Token {
                ty: TokenType::Identifier(id),
                span,
            } => {
                let node = AstIdentifier { name: id, span };
                Ok(node)
            }
            _ => Err(ParseError::from(UnexpectedTokenError {
                span: token.span,
                token,
            })),
        }
    }

    /// Parse a type.
    ///
    /// ```text
    /// type ::= named_type | pointer_type | builtin_unit_type | builtin_integer32_type
    ///
    /// builtin_unit_type ::= identifier<"unit">
    /// builtin_integer32_type ::= identifier<"i32">
    /// ```
    pub fn parse_type(&mut self) -> ParseResult<AstType<'ast>> {
        let token = self.lookahead_or_err()?;
        match &token.ty {
            // If it is a named type, we can test if it's matching one of the builtin types.
            TokenType::Identifier(v) => match v.as_str() {
                "i32" => {
                    let id = self.parse_identifier()?;
                    let node = AstInteger32Type { span: id.span };
                    Ok(AstType::Integer32(node))
                }
                "bool" => {
                    let id = self.parse_identifier()?;
                    let node = AstBooleanType { span: id.span };
                    Ok(AstType::Boolean(node))
                }
                "unit" => {
                    let id = self.parse_identifier()?;
                    let node = AstUnitType { span: id.span };
                    Ok(AstType::Unit(node))
                }
                _ => Ok(AstType::Named(self.parse_named_type()?)),
            },
            TokenType::Star => Ok(AstType::Pointer(self.parse_pointer_type()?)),
            _ => {
                let token = self.eat()?;
                Err(ParseError::from(UnexpectedTokenError {
                    span: token.span,
                    token,
                }))
            }
        }
    }

    /// Parse a named type.
    ///
    /// ```text
    /// named_type ::= identifier
    /// ```
    pub fn parse_named_type(&mut self) -> ParseResult<AstNamedType<'ast>> {
        let id = self.parse_identifier()?;
        let node = AstNamedType {
            span: id.span,
            name: self.arena.alloc(id),
        };
        Ok(node)
    }

    /// Parse a pointer type of single indirection.
    ///
    /// ```text
    /// pointer_type ::= STAR type
    /// ```
    pub fn parse_pointer_type(&mut self) -> ParseResult<AstPointerType<'ast>> {
        let indirection = self.check(&TokenType::Star)?;
        let inner = self.parse_type()?;
        let node = AstPointerType {
            span: Span::from_pair(&indirection.span, inner.span()),
            inner: self.arena.alloc(inner),
        };
        Ok(node)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBinaryOp, AstBreakStmt, AstContinueStmt, AstExpr, AstIdentifier, AstType, AstUnaryOp,
    };
    use crate::error::{InvalidIntegerLiteralError, ParseError};
    
    use eight_macros::{assert_err, assert_matches, assert_none, assert_ok, assert_some};
    use eight_span::Span;

    macro_rules! assert_parse {
        ($input:expr, $body:expr) => {{
            use crate::arena::AstArena;
            use crate::lexer::Lexer;
            use crate::parser::Parser;

            let mut lexer = Lexer::new($input);
            let arena = AstArena::default();
            let mut parser = Parser::new(&mut lexer, &arena);
            $body(&mut parser);
            // Ensure there are no more items in the parser
            let next = assert_ok!(parser.lookahead());
            assert!(next.is_none(), "expected end of stream, got {:?}", next);
        }};
    }

    #[test]
    fn test_parse_builtin_type() {
        assert_parse!("i32", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstType::Integer32(_)));
        });

        assert_parse!("unit", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstType::Unit(_)));
        });

        assert_parse!("bool", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstType::Boolean(_)));
        });
    }

    #[test]
    fn test_parse_named_type() {
        assert_parse!("Matrix", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            assert_eq!(production.span(), &Span::new(0..6));
            assert!(matches!(production, AstType::Named(inner) if inner.name.name == "Matrix"));
        });
    }

    #[test]
    fn test_parse_pointer_type() {
        assert_parse!("*i32", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            let pointer = assert_matches!(production, AstType::Pointer(p) => p);
            assert!(matches!(pointer.inner, AstType::Integer32(_)));
        });

        assert_parse!("**i32", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            let pointer = assert_matches!(production, AstType::Pointer(p) => p);
            let inner = assert_matches!(pointer.inner, AstType::Pointer(p) => p);
            assert!(matches!(inner.inner, AstType::Integer32(_)));
        });

        assert_parse!("*vec2", |p: &mut Parser| {
            let production = p.parse_type();
            let production = assert_ok!(production);
            let pointer = assert_matches!(production, AstType::Pointer(p) => p);
            assert!(matches!(pointer.inner, AstType::Named(name) if name.name.name == "vec2"));
        });
    }

    #[test]
    fn test_parse_struct_member_item() {
        assert_parse!("x: i32,", |p: &mut Parser| {
            let production = p.parse_type_member_item();
            let production = assert_ok!(production);
            let name = production.name;
            let ty = production.ty;

            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            assert!(matches!(&ty, AstType::Integer32(_)));
        });

        assert_parse!("x: *matrix,", |p: &mut Parser| {
            let production = p.parse_type_member_item();
            let production = assert_ok!(production);
            let name = production.name;
            let ty = production.ty;

            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            assert!(matches!(&ty, AstType::Pointer(_)));

            let ptr = assert_matches!(ty, AstType::Pointer(p) => p);
            assert!(matches!(ptr.inner, AstType::Named(name) if name.name.name == "matrix"));
        });
    }

    #[test]
    fn test_parse_struct_item() {
        assert_parse!("struct Matrix { x: i32, y: i32, }", |p: &mut Parser| {
            let production = p.parse_struct_item();
            let production = assert_ok!(production);
            let name = production.name;
            let members = production.members;
            assert_eq!(members.len(), 2);

            assert!(matches!(name, AstIdentifier { name, .. } if name == "Matrix"));
        });

        assert_parse!(
            "struct Matrix { x: i32, y: i32, z: *vec2, }",
            |p: &mut Parser| {
                let production = p.parse_struct_item();
                let production = assert_ok!(production);
                let name = production.name;
                let members = production.members;
                assert_eq!(members.len(), 3);

                assert!(matches!(name, AstIdentifier { name, .. } if name == "Matrix"));
            }
        );
    }

    #[test]
    fn test_parse_fn_parameter_item() {
        assert_parse!("x: i32", |p: &mut Parser| {
            let production = p.parse_fn_parameter_item();
            let production = assert_ok!(production);
            let name = production.name;
            let ty = production.ty;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            assert!(matches!(&ty, AstType::Integer32(_)));
        });
    }

    #[test]
    fn test_parse_fn_item() {
        assert_parse!("fn x(x: i32) -> i32 {}", |p: &mut Parser| {
            let production = p.parse_fn_item();
            let production = assert_ok!(production);
            let name = production.name;
            let parameters = production.parameters;
            let return_type = assert_some!(production.return_type);
            let body = production.body;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            assert_eq!(parameters.len(), 1);
            assert!(matches!(return_type, AstType::Integer32(_)));
            assert_eq!(body.len(), 0);
        });

        assert_parse!("fn zzz(y: *i32) {}", |p: &mut Parser| {
            let production = p.parse_fn_item();
            let production = assert_ok!(production);
            let name = production.name;
            let parameters = production.parameters;
            assert_none!(production.return_type);
            let body = production.body;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "zzz"));
            assert_eq!(parameters.len(), 1);
            assert_eq!(body.len(), 0);
        });

        assert_parse!("fn v(x: i32, y: i32) {}", |p: &mut Parser| {
            let production = p.parse_fn_item();
            let production = assert_ok!(production);
            let parameters = production.parameters;
            assert_eq!(parameters.len(), 2);
        });

        assert_parse!("fn foo() {}", |p: &mut Parser| {
            let production = p.parse_fn_item();
            let production = assert_ok!(production);
            let parameters = production.parameters;
            assert_eq!(parameters.len(), 0);
        });
    }

    #[test]
    fn test_parse_fn_item_with_type_parameters() {
        assert_parse!("fn foo<T, U>() {}", |p: &mut Parser| {
            let production = p.parse_fn_item();
            let production = assert_ok!(production);
            let type_parameters = production.type_parameters;
            assert_eq!(type_parameters.len(), 2);
        });
    }

    #[test]
    fn test_parse_type_parameter_item() {
        assert_parse!("T", |p: &mut Parser| {
            let production = p.parse_type_parameter_item();
            let production = assert_ok!(production);
            let name = production.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "T"));
        });
    }

    #[test]
    fn test_parse_intrinsic_fn_item() {
        assert_parse!("intrinsic_fn foo(x: i32) -> i32;", |p: &mut Parser| {
            let production = p.parse_intrinsic_fn_item();
            let production = assert_ok!(production);
            let name = production.name;
            let parameters = production.parameters;
            let return_type = production.return_type;
            assert_eq!(name.name, "foo");
            assert_eq!(parameters.len(), 1);
            assert!(matches!(return_type, AstType::Integer32(_)));
        });
    }

    #[test]
    fn test_parse_intrinsic_fn_item_with_type_parameters() {
        assert_parse!("intrinsic_fn malloc<T>() -> *T;", |p: &mut Parser| {
            let production = p.parse_intrinsic_fn_item();
            let production = assert_ok!(production);
            let type_parameters = production.type_parameters;
            assert_eq!(type_parameters.len(), 1);
        });
    }

    #[test]
    fn test_parse_intrinsic_type_item() {
        assert_parse!("intrinsic_type i32;", |p: &mut Parser| {
            let production = p.parse_intrinsic_type_item();
            let production = assert_ok!(production);
            let name = production.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "i32"));
        });
    }

    #[test]
    fn test_parse_trait_item() {
        assert_parse!("trait Foo<K> { fn bar() -> K; }", |p: &mut Parser| {
            let production = p.parse_trait_item();
            let production = assert_ok!(production);
            let name = production.name;
            let type_parameters = production.type_parameters;
            let members = production.members;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "Foo"));
            assert_eq!(type_parameters.len(), 1);
            assert_eq!(members.len(), 1);
        });
    }

    #[test]
    fn test_parse_instance_item() {
        assert_parse!(
            "instance Foo<i32> { fn bar() -> i32 { return 0; } }",
            |p: &mut Parser| {
                let production = p.parse_instance_item();
                let production = assert_ok!(production);
                let name = production.name;
                let instantiation_type_parameters = production.instantiation_type_parameters;
                let members = production.members;
                assert!(matches!(name, AstIdentifier { name, .. } if name == "Foo"));
                assert_eq!(instantiation_type_parameters.len(), 1);
                assert_eq!(members.len(), 1);
            }
        );
    }

    #[test]
    fn test_parse_let_stmt() {
        assert_parse!("let x = 1;", |p: &mut Parser| {
            let production = p.parse_let_stmt();
            let production = assert_ok!(production);
            let name = production.name;
            let initializer = production.value;
            let ty = production.ty;
            assert_eq!(name.name, "x");
            assert!(matches!(initializer, AstExpr::IntegerLiteral(_)));
            assert_none!(ty);
        });

        assert_parse!("let x: i32 = 1;", |p: &mut Parser| {
            let production = p.parse_let_stmt();
            let production = assert_ok!(production);
            let ty = production.ty;
            let ty = assert_some!(ty);
            assert!(matches!(&ty, AstType::Integer32(_)));
        });
    }

    #[test]
    fn test_parse_return_stmt() {
        assert_parse!("return;", |p: &mut Parser| {
            let production = p.parse_return_stmt();
            let production = assert_ok!(production);
            assert_none!(production.value);
        });

        assert_parse!("return 1;", |p: &mut Parser| {
            let production = p.parse_return_stmt();
            let production = assert_ok!(production);
            let value = assert_some!(production.value);
            assert!(matches!(&value, AstExpr::IntegerLiteral(_)));
        });
    }

    #[test]
    fn test_parse_for_stmt() {
        assert_parse!("for (;;) {}", |p: &mut Parser| {
            let production = p.parse_for_stmt();
            let production = assert_ok!(production);
            assert_none!(production.initializer);
            assert_none!(production.condition);
            assert_none!(production.increment);
            let body = production.body;
            assert_eq!(body.len(), 0);
        });

        assert_parse!(
            "for (let x = 1; x < 10; x = x + 1) { x; }",
            |p: &mut Parser| {
                let production = p.parse_for_stmt();
                let production = assert_ok!(production);
                assert_some!(production.initializer);
                assert_some!(production.condition);
                assert_some!(production.increment);
                let body = production.body;
                assert_eq!(body.len(), 1);
            }
        );
    }

    #[test]
    fn test_parse_break_stmt() {
        assert_parse!("break;", |p: &mut Parser| {
            let production = p.parse_break_stmt();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstBreakStmt { .. }));
        });
    }

    #[test]
    fn test_parse_continue_stmt() {
        assert_parse!("continue;", |p: &mut Parser| {
            let production = p.parse_continue_stmt();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstContinueStmt { .. }));
        });
    }

    #[test]
    fn test_parse_if_stmt() {
        assert_parse!("if (x) {}", |p: &mut Parser| {
            let production = p.parse_if_stmt();
            let production = assert_ok!(production);
            let condition = production.condition;
            let body = production.happy_path;
            assert!(matches!(condition, AstExpr::Reference(_)));
            let condition = assert_matches!(condition, AstExpr::Reference(condition) => condition);
            assert!(matches!(condition.name, AstIdentifier { name, .. } if name == "x"));
            assert_eq!(body.len(), 0);
        });

        assert_parse!("if (x) { y(); } else { z(); }", |p: &mut Parser| {
            let production = p.parse_if_stmt();
            let production = assert_ok!(production);
            assert_some!(production.unhappy_path);
        });
    }

    #[test]
    fn test_parse_expr_stmt() {
        assert_parse!("x;", |p: &mut Parser| {
            let production = p.parse_expr_stmt();
            let production = assert_ok!(production);
            let expr = production.expr;
            assert!(matches!(expr, AstExpr::Reference(_)));
            let expr = assert_matches!(expr, AstExpr::Reference(expr) => expr);
            let name = expr.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        });
    }

    #[test]
    fn test_parse_group_expr() {
        assert_parse!("(x)", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Group(_)));
            let inner = assert_matches!(production, AstExpr::Group(inner) => inner);
            let inner = inner.inner;
            assert!(matches!(inner, AstExpr::Reference(_)));
        });
    }

    #[test]
    fn test_parse_reference_expr() {
        assert_parse!("x", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Reference(_)));
            let inner = assert_matches!(production, AstExpr::Reference(inner) => inner);
            let name = inner.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        });

        assert_parse!("  x  ", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert_eq!(production.span(), &Span::new(2..3));
        });
    }

    #[test]
    fn test_parse_literal_expr() {
        assert_parse!("123", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::IntegerLiteral(_)));
            let inner = assert_matches!(production, AstExpr::IntegerLiteral(inner) => inner);
            let value = inner.value;
            assert_eq!(value, 123);
        });

        assert_parse!("true", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BooleanLiteral(_)));
            let inner = assert_matches!(production, AstExpr::BooleanLiteral(inner) => inner);
            let value = inner.value;
            assert!(value);
        });

        assert_parse!("false", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BooleanLiteral(_)));
            let inner = assert_matches!(production, AstExpr::BooleanLiteral(inner) => inner);
            let value = inner.value;
            assert!(!value);
        });
    }

    #[test]
    fn test_parse_dot_index_expr() {
        assert_parse!("x.y", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::DotIndex(_)));
            let inner = assert_matches!(production, AstExpr::DotIndex(inner) => inner);
            let origin = inner.origin;
            assert!(matches!(origin, AstExpr::Reference(_)));
            let origin = assert_matches!(origin, AstExpr::Reference(origin) => origin);
            let name = origin.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            assert_eq!(inner.index.name, "y");
        });
    }

    #[test]
    fn test_parse_bracket_index_expr() {
        assert_parse!("x[y]", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BracketIndex(_)));
            let inner = assert_matches!(production, AstExpr::BracketIndex(inner) => inner);
            let origin = inner.origin;
            assert!(matches!(origin, AstExpr::Reference(_)));
            let origin = assert_matches!(origin, AstExpr::Reference(origin) => origin);
            let name = origin.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            let index = assert_matches!(inner.index, AstExpr::Reference(index) => index);
            assert!(matches!(index.name, AstIdentifier { name, .. } if name == "y"));
        });
    }

    #[test]
    fn test_parse_call_expr() {
        assert_parse!("x()", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert_eq!(production.span(), &Span::new(0..3));
            assert!(matches!(&production, AstExpr::Call(_)));
            let inner = assert_matches!(production, AstExpr::Call(inner) => inner);
            let origin = inner.callee;
            let origin = assert_matches!(origin, AstExpr::Reference(origin) => origin);
            let name = origin.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        });

        assert_parse!("x(z)", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Call(_)));
            let inner = assert_matches!(production, AstExpr::Call(inner) => inner);
            let count = inner.arguments.len();
            assert_eq!(count, 1);
        });

        assert_parse!("x(z, foo(bar, baz()))", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert_eq!(production.span(), &Span::new(0..21));
            assert!(matches!(&production, AstExpr::Call(_)));
            let inner = assert_matches!(production, AstExpr::Call(inner) => inner);
            assert_eq!(inner.arguments.len(), 2);
        });
    }

    #[test]
    fn test_parse_chained_postfix_expr() {
        assert_parse!("x[y.k]().www[z]", |p: &mut Parser| {
            let production = p.parse_expr();
            assert_ok!(production);
        });
    }

    #[test]
    fn test_parse_call_expr_with_type_arguments() {
        assert_parse!("x::<i32, bool>()", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Call(_)));
            let inner = assert_matches!(production, AstExpr::Call(inner) => inner);
            let count = inner.type_arguments.len();
            assert_eq!(count, 2);
            assert!(matches!(&inner.type_arguments[0], AstType::Integer32(_)));
            assert!(matches!(&inner.type_arguments[1], AstType::Boolean(_)));
        });
    }

    #[test]
    fn test_parse_call_expr_with_turbo_fish_zero_types() {
        assert_parse!("x::<>()", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Call(_)));
            let inner = assert_matches!(production, AstExpr::Call(inner) => inner);
            let count = inner.type_arguments.len();
            assert_eq!(count, 0);
        });
    }

    #[test]
    fn test_parse_construct_expr() {
        assert_parse!("new x {}", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Construct(_)));
            let inner = assert_matches!(production, AstExpr::Construct(inner) => inner);
            let count = inner.arguments.len();
            assert_eq!(count, 0);
        });

        assert_parse!("new x { y: z }", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Construct(_)));
            let inner = assert_matches!(production, AstExpr::Construct(inner) => inner);
            let count = inner.arguments.len();
            assert_eq!(count, 1);
        });

        assert_parse!("new x { y: notrailingcomma }", |p: &mut Parser| {
            let production = p.parse_expr();
            assert_ok!(production);
        });
    }

    #[test]
    fn test_parse_constructor_grammar_allows_non_id_types() {
        assert_parse!("new *x {}", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Construct(_)));
        });
    }

    #[test]
    fn test_parse_unary_expr() {
        assert_parse!("-x", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::UnaryOp(_)));
            let inner = assert_matches!(production, AstExpr::UnaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstUnaryOp::Neg);
        });

        assert_parse!("*x", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::UnaryOp(_)));
            let inner = assert_matches!(production, AstExpr::UnaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstUnaryOp::Deref);
        });

        assert_parse!("&x", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::UnaryOp(_)));
            let inner = assert_matches!(production, AstExpr::UnaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstUnaryOp::AddressOf);
        });
    }

    #[test]
    fn test_parse_multiplicative_expr() {
        assert_parse!("x + y", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Add);
        });

        assert_parse!("x * y / z", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Mul);
        });
    }

    #[test]
    fn test_parse_additive_expr() {
        assert_parse!("x - y", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Sub);
        });

        assert_parse!("x + y * z", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Add);
            let rhs = inner.rhs;
            let inner = assert_matches!(rhs, AstExpr::BinaryOp(inner) => inner);
            assert_eq!(inner.op, AstBinaryOp::Mul);
        });
    }

    #[test]
    fn test_parse_comparison_expr() {
        assert_parse!("x < y", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Lt);
        });

        assert_parse!("x < y < z", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::BinaryOp(_)));
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Lt);
            let rhs = inner.rhs;
            let inner = assert_matches!(rhs, AstExpr::BinaryOp(inner) => inner);
            assert_eq!(inner.op, AstBinaryOp::Lt);
        });
    }

    #[test]
    fn test_parse_logical_and_expr() {
        assert_parse!("a + 3 && y", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::And);
        });
    }

    #[test]
    fn test_parse_logical_or_expr() {
        assert_parse!("a || y()", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            let inner = assert_matches!(production, AstExpr::BinaryOp(inner) => inner);
            let op = inner.op;
            assert_eq!(op, AstBinaryOp::Or);
        });
    }

    #[test]
    fn test_parse_assign_expr() {
        assert_parse!("a = 3", |p: &mut Parser| {
            let production = p.parse_expr();
            let production = assert_ok!(production);
            assert!(matches!(&production, AstExpr::Assign(_)));
        });
    }

    #[test]
    fn test_parse_invalid_literal() {
        assert_parse!("let k = 1234773457276345671237572345", |p: &mut Parser| {
            let production = p.parse_let_stmt();
            let production = assert_err!(production);
            assert!(
                matches!(production, ParseError::InvalidIntegerLiteral(InvalidIntegerLiteralError {
                    span, ..
                }) if span.low == 8 && span.high == 36)
            );
        });
    }

    #[test]
    fn test_parse_comment() {
        assert_parse!("struct Module {// foo\n}", |p: &mut Parser| {
            let production = p.parse_struct_item();
            let production = assert_ok!(production);
            assert_eq!(production.span, Span::new(0..23));
        });

        assert_parse!("struct Module // foo\n{}", |p: &mut Parser| {
            let production = p.parse_struct_item();
            let production = assert_ok!(production);
            assert_eq!(production.span, Span::new(0..23));
        });
    }
}
