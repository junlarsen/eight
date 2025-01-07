use crate::ast::{
    AstAssignExpr, AstBinaryOp, AstBinaryOpExpr, AstBracketIndexExpr, AstBreakStmt, AstCallExpr,
    AstConstructExpr, AstConstructorExprArgument, AstContinueStmt, AstDotIndexExpr, AstExpr,
    AstExprStmt, AstForStmt, AstForStmtInitializer, AstFunctionItem, AstFunctionParameterItem,
    AstGroupExpr, AstIdentifier, AstIfStmt, AstInteger32Type, AstIntegerLiteralExpr, AstItem,
    AstLetStmt, AstNamedType, AstPointerType, AstReferenceExpr, AstReturnStmt, AstStmt,
    AstTranslationUnit, AstType, AstTypeItem, AstTypeMemberItem, AstUnaryOp, AstUnaryOpExpr,
    AstUnitType,
};
use crate::lexer::Lexer;
use crate::{
    AstBooleanLiteralExpr, AstBooleanType, AstFunctionTypeParameterItem, AstIntrinsicFunctionItem,
    AstIntrinsicScalarItem, ParseError, ParseResult, Token, TokenType, UnexpectedEndOfFileError,
    UnexpectedTokenError,
};
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
            self.la = match self.lexer.produce() {
                Ok(tok) => Some(tok),
                // If the end of source is reached, we might be able to recover. For example, if
                // statements may or may not have an `else` after them.
                Err(ParseError::UnexpectedEndOfFile(_)) => None,
                Err(err) => return Err(err),
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
        self.lexer.produce()
    }
}

pub struct Parser<'a> {
    input: ParserInput<'a>,
}

impl<'a> Parser<'a> {
    /// Create a new parser from a given lexer.
    ///
    /// The current grammar will make consume the entire lexer, but in the future, we may support
    /// partial parsing, so taking ownership of the lexer is not a requirement.
    pub fn new(lexer: &'a mut Lexer<'a>) -> Self {
        Self {
            input: ParserInput::new(lexer),
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
    pub fn parser_combinator_delimited<T, F>(
        &mut self,
        delimiter: &TokenType,
        circuit_breaker: &TokenType,
        f: F,
    ) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Parser) -> ParseResult<T>,
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
        F: FnOnce(&mut Parser) -> ParseResult<T>,
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
        F: Fn(&mut Parser) -> ParseResult<T>,
    {
        let mut items = Vec::new();
        while !self.lookahead_check(circuit_breaker)? {
            items.push(f(self)?);
        }
        Ok(items)
    }
}

impl Parser<'_> {
    /// Top-level entry for parsing a translation unit (file).
    pub fn parse(&mut self) -> ParseResult<AstTranslationUnit> {
        self.parse_translation_unit()
    }

    /// Parse a translation unit.
    ///
    /// ```text
    /// translation_unit ::= item*
    /// ```
    pub fn parse_translation_unit(&mut self) -> ParseResult<AstTranslationUnit> {
        let mut items = Vec::new();
        while self.lookahead()?.is_some() {
            items.push(self.parse_item()?);
        }
        // The translation unit doesn't record a span
        let node = AstTranslationUnit { items };
        Ok(node)
    }

    /// Parse an item.
    ///
    /// ```text
    /// item ::= fn_item | type_item | intrinsic_fn_item
    /// ```
    pub fn parse_item(&mut self) -> ParseResult<AstItem> {
        let token = self.lookahead_or_err()?;
        let node = match token.ty {
            TokenType::KeywordFn => AstItem::Function(self.parse_fn_item()?),
            TokenType::KeywordType => AstItem::Type(self.parse_type_item()?),
            TokenType::KeywordIntrinsicFn => {
                AstItem::IntrinsicFunction(self.parse_intrinsic_fn_item()?)
            }
            TokenType::KeywordIntrinsicScalar => {
                AstItem::IntrinsicScalar(self.parse_intrinsic_scalar_item()?)
            }
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
    ///             (OPEN_ANGLE ((fn_type_parameter_item COMMA)+ fn_type_parameter_item)? CLOSE_ANGLE)?
    ///             OPEN_PAREN ((fn_parameter_item COMMA)+ fn_parameter_item)? CLOSE_PAREN
    ///             CLOSE_PAREN (ARROW type)? OPEN_BRACE stmt* CLOSE_BRACE
    /// ```
    pub fn parse_fn_item(&mut self) -> ParseResult<AstFunctionItem> {
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
                        |p| p.parse_fn_type_parameter_item(),
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
            name: id,
            parameters,
            type_parameters,
            return_type,
            body,
        };
        Ok(node)
    }

    /// Parse a function parameter item.
    ///
    /// ```text
    /// fn_parameter_item ::= identifier COLON type
    /// ```
    pub fn parse_fn_parameter_item(&mut self) -> ParseResult<AstFunctionParameterItem> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let ty = self.parse_type()?;
        let node = AstFunctionParameterItem {
            span: Span::from_pair(&id.span, ty.span()),
            name: id,
            ty,
        };
        Ok(node)
    }

    /// Parse a function type parameter item.
    ///
    /// ```text
    /// fn_type_parameter_item ::= identifier
    /// ```
    pub fn parse_fn_type_parameter_item(&mut self) -> ParseResult<AstFunctionTypeParameterItem> {
        let id = self.parse_identifier()?;
        let node = AstFunctionTypeParameterItem {
            span: id.span,
            name: id,
        };
        Ok(node)
    }

    /// Parse a type item.
    ///
    /// ```text
    /// type_item ::= KEYWORD_TYPE identifier EQUAL OPEN_BRACE type_member_item* CLOSE_BRACE
    /// ```
    pub fn parse_type_item(&mut self) -> ParseResult<AstTypeItem> {
        let start = self.check(&TokenType::KeywordType)?;
        let id = self.parse_identifier()?;
        self.check(&TokenType::Equal)?;
        self.check(&TokenType::OpenBrace)?;
        let members =
            self.parser_combinator_many(&TokenType::CloseBrace, |p| p.parse_type_member_item())?;
        let end = self.check(&TokenType::CloseBrace)?;
        let node = AstTypeItem {
            span: Span::from_pair(&start.span, &end.span),
            name: id,
            members,
        };
        Ok(node)
    }

    /// Parse a type member item.
    ///
    /// ```text
    /// type_member_item ::= identifier COLON type COMMA
    /// ```
    pub fn parse_type_member_item(&mut self) -> ParseResult<AstTypeMemberItem> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let ty = self.parse_type()?;
        let end = self.check(&TokenType::Comma)?;
        let node = AstTypeMemberItem {
            span: Span::from_pair(&id.span, &end.span),
            name: id,
            ty,
        };
        Ok(node)
    }

    /// Parse an intrinsic function item.
    ///
    /// Unlike regular functions, intrinsic functions must have their return type specified.
    ///
    /// ```text
    /// intrinsic_fn_item ::= KEYWORD_INTRINSIC_FN IDENTIFIER
    ///                       (OPEN_ANGLE ((fn_type_parameter_item COMMA)+ fn_type_parameter_item)? CLOSE_ANGLE)?
    ///                       OPEN_PAREN ((fn_parameter_item COMMA)+ fn_parameter_item)? CLOSE_PAREN
    ///                       ARROW type SEMICOLON
    /// ```
    pub fn parse_intrinsic_fn_item(&mut self) -> ParseResult<AstIntrinsicFunctionItem> {
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
                        |p| p.parse_fn_type_parameter_item(),
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
            name: id,
            parameters,
            type_parameters,
            return_type,
        };
        Ok(node)
    }

    /// Parse an intrinsic scalar item.
    ///
    /// ```text
    /// intrinsic_scalar_item ::= KEYWORD_INTRINSIC_FN IDENTIFIER SEMICOLON
    /// ```
    pub fn parse_intrinsic_scalar_item(&mut self) -> ParseResult<AstIntrinsicScalarItem> {
        let start = self.check(&TokenType::KeywordIntrinsicScalar)?;
        let id = self.parse_identifier()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstIntrinsicScalarItem {
            span: Span::from_pair(&start.span, &end.span),
            name: id,
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
    pub fn parse_stmt(&mut self) -> ParseResult<AstStmt> {
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
    pub fn parse_let_stmt(&mut self) -> ParseResult<AstLetStmt> {
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
            name: id,
            ty,
            value: expr,
        };
        Ok(node)
    }

    /// Parses a return statement.
    ///
    /// ```text
    /// return_stmt ::= RETURN expr? SEMICOLON
    /// ```
    pub fn parse_return_stmt(&mut self) -> ParseResult<AstReturnStmt> {
        let start = self.check(&TokenType::KeywordReturn)?;
        let value =
            self.parser_combinator_take_if(|t| t.ty != TokenType::Semicolon, |p| p.parse_expr())?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstReturnStmt {
            span: Span::from_pair(&start.span, &end.span),
            value,
        };
        Ok(node)
    }

    /// Parses a for statement.
    ///
    /// ```text
    /// for_stmt ::= FOR LPAREN for_stmt_initializer? SEMICOLON expr? SEMICOLON expr? RPAREN LBRACE stmt* RBRACE
    /// ```
    pub fn parse_for_stmt(&mut self) -> ParseResult<AstForStmt> {
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
            initializer,
            condition,
            increment,
            body,
        };
        Ok(node)
    }

    /// Parses a for statement initializer.
    ///
    /// ```text
    /// for_stmt_initializer ::= LET identifier EQUAL expr
    /// ```
    pub fn parse_for_stmt_initializer(&mut self) -> ParseResult<AstForStmtInitializer> {
        let start = self.check(&TokenType::KeywordLet)?;
        let name = self.parse_identifier()?;
        self.check(&TokenType::Equal)?;
        let initializer = self.parse_expr()?;
        let node = AstForStmtInitializer {
            span: Span::from_pair(&start.span, initializer.span()),
            name,
            initializer,
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
    pub fn parse_if_stmt(&mut self) -> ParseResult<AstIfStmt> {
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
            condition,
            happy_path: body,
            unhappy_path: r#else,
        };
        Ok(node)
    }

    /// Parses an expression statement.
    ///
    /// ```text
    /// expr_stmt ::= expr SEMICOLON
    pub fn parse_expr_stmt(&mut self) -> ParseResult<AstExprStmt> {
        let expr = self.parse_expr()?;
        let end = self.check(&TokenType::Semicolon)?;
        let node = AstExprStmt {
            span: Span::from_pair(expr.span(), &end.span),
            expr,
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
    /// 4. DotIndex Expression
    /// 4. BracketIndex Expression
    /// 5. Call Expression
    /// 6. Construct Expression
    /// 7. Unary Expression
    /// 8. Multiplicative Expression
    /// 9. Additive Expression
    /// 10. Binary Expression
    /// 11. Comparison Expression
    /// 12. Logical And Expression
    /// 13. Logical Or Expression
    /// 14. Assign Expression
    ///
    /// [precedence_climber]: https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
    pub fn parse_expr(&mut self) -> ParseResult<AstExpr> {
        self.parse_assign_expr()
    }

    /// Parse an assignment expression.
    ///
    /// ```text
    /// assign_expr ::= logical_expr EQUAL assign_expr
    /// ```
    pub fn parse_assign_expr(&mut self) -> ParseResult<AstExpr> {
        let expr = self.parse_logical_or_expr()?;

        if self.lookahead_check(&TokenType::Equal)? {
            self.check(&TokenType::Equal)?;
            let rhs = self.parse_assign_expr()?;
            let node = AstAssignExpr {
                span: Span::from_pair(expr.span(), rhs.span()),
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
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
    pub fn parse_logical_or_expr(&mut self) -> ParseResult<AstExpr> {
        let lhs = self.parse_logical_and_expr()?;

        if self.lookahead_check(&TokenType::LogicalOr)? {
            self.check(&TokenType::LogicalOr)?;
            let rhs = self.parse_logical_or_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: AstBinaryOp::Or,
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
    pub fn parse_logical_and_expr(&mut self) -> ParseResult<AstExpr> {
        let lhs = self.parse_comparison_expr()?;

        if self.lookahead_check(&TokenType::LogicalAnd)? {
            self.check(&TokenType::LogicalAnd)?;
            let rhs = self.parse_logical_and_expr()?;
            let node = AstBinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op: AstBinaryOp::And,
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
    pub fn parse_comparison_expr(&mut self) -> ParseResult<AstExpr> {
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
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
    pub fn parse_additive_expr(&mut self) -> ParseResult<AstExpr> {
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
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
    pub fn parse_multiplicative_expr(&mut self) -> ParseResult<AstExpr> {
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
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
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
    pub fn parse_unary_expr(&mut self) -> ParseResult<AstExpr> {
        let token = self.lookahead_or_err()?;

        match token.ty {
            TokenType::Minus => {
                let op = self.check(&TokenType::Minus)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: Box::new(rhs),
                    op: AstUnaryOp::Neg,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::Bang => {
                let op = self.check(&TokenType::Bang)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: Box::new(rhs),
                    op: AstUnaryOp::Not,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::Star => {
                let op = self.check(&TokenType::Star)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: Box::new(rhs),
                    op: AstUnaryOp::Deref,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            TokenType::AddressOf => {
                let op = self.check(&TokenType::AddressOf)?;
                let rhs = self.parse_unary_expr()?;
                let node = AstUnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    operand: Box::new(rhs),
                    op: AstUnaryOp::AddressOf,
                };
                Ok(AstExpr::UnaryOp(node))
            }
            _ => self.parse_call_expr(),
        }
    }

    /// Parse a call expression.
    ///
    /// ```text
    /// call_expr ::= construct_expr
    ///               (COLON_COLON OPEN_ANGLE (type (COMMA type)*)? CLOSE_ANGLE)?
    ///               (OPEN_PAREN (expr (COMMA expr)*)? CLOSE_PAREN)?
    /// ```
    pub fn parse_call_expr(&mut self) -> ParseResult<AstExpr> {
        let callee = self.parse_construct_expr()?;
        let is_turbo_fish = self.lookahead_check(&TokenType::ColonColon)?;
        if self.lookahead_check(&TokenType::OpenParen)? || is_turbo_fish {
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
            let arguments =
                self.parser_combinator_delimited(&TokenType::Comma, &TokenType::CloseParen, |p| {
                    p.parse_expr()
                })?;
            let end = self.check(&TokenType::CloseParen)?;
            let node = AstCallExpr {
                span: Span::from_pair(callee.span(), &end.span),
                callee: Box::new(callee),
                arguments,
                type_arguments,
            };
            return Ok(AstExpr::Call(node));
        };

        Ok(callee)
    }

    /// Parse a construct expression.
    ///
    /// ```text
    /// construct_expr ::= NEW type OPEN_BRACE
    ///                   (construct_expr_argument (COMMA construct_expr_argument)*)?
    ///                   CLOSE_BRACE
    /// ```
    pub fn parse_construct_expr(&mut self) -> ParseResult<AstExpr> {
        if !self.lookahead_check(&TokenType::KeywordNew)? {
            return self.parse_bracket_index_expr();
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
            callee,
            arguments,
        };
        Ok(AstExpr::Construct(node))
    }

    /// Parse a construct expression argument.
    ///
    /// ```text
    /// construct_expr_argument ::= identifier COLON expr
    pub fn parse_construct_expr_argument(&mut self) -> ParseResult<AstConstructorExprArgument> {
        let id = self.parse_identifier()?;
        self.check(&TokenType::Colon)?;
        let expr = self.parse_expr()?;
        let node = AstConstructorExprArgument {
            span: Span::from_pair(&id.span, expr.span()),
            field: id,
            expr,
        };
        Ok(node)
    }

    /// Parse a bracket index expression.
    ///
    /// ```text
    /// bracket_index_expr ::= reference_expr OPEN_BRACKET expr CLOSE_BRACKET
    /// ```
    pub fn parse_bracket_index_expr(&mut self) -> ParseResult<AstExpr> {
        let origin = self.parse_dot_index_expr()?;

        if self.lookahead_check(&TokenType::OpenBracket)? {
            self.check(&TokenType::OpenBracket)?;
            let index = self.parse_expr()?;
            let end = self.check(&TokenType::CloseBracket)?;
            let node = AstBracketIndexExpr {
                span: Span::from_pair(origin.span(), &end.span),
                origin: Box::new(origin),
                index: Box::new(index),
            };
            return Ok(AstExpr::BracketIndex(node));
        }

        Ok(origin)
    }

    /// Parse a dot index expression.
    ///
    /// ```text
    /// dot_index_expr ::= reference_expr DOT identifier
    /// ```
    pub fn parse_dot_index_expr(&mut self) -> ParseResult<AstExpr> {
        let origin = self.parse_reference_expr()?;

        if self.lookahead_check(&TokenType::Dot)? {
            self.check(&TokenType::Dot)?;
            let index = self.parse_identifier()?;
            let node = AstDotIndexExpr {
                span: Span::from_pair(origin.span(), &index.span),
                origin: Box::new(origin),
                index,
            };
            return Ok(AstExpr::DotIndex(node));
        }

        Ok(origin)
    }

    /// Parse a reference expression.
    ///
    /// ```text
    /// reference_expr ::= identifier | group_expr
    /// ```
    pub fn parse_reference_expr(&mut self) -> ParseResult<AstExpr> {
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
                name: id,
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
    pub fn parse_literal_expr(&mut self) -> ParseResult<AstExpr> {
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
    pub fn parse_group_expr(&mut self) -> ParseResult<AstExpr> {
        if self.lookahead_check(&TokenType::OpenParen)? {
            let start = self.check(&TokenType::OpenParen)?;
            let inner = self.parse_expr()?;
            let end = self.check(&TokenType::CloseParen)?;
            let node = AstGroupExpr {
                span: Span::from_pair(&start.span, &end.span),
                inner: Box::new(inner),
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
    pub fn parse_type(&mut self) -> ParseResult<AstType> {
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
    pub fn parse_named_type(&mut self) -> ParseResult<AstNamedType> {
        let id = self.parse_identifier()?;
        let node = AstNamedType {
            span: id.span,
            name: id,
        };
        Ok(node)
    }

    /// Parse a pointer type of single indirection.
    ///
    /// ```text
    /// pointer_type ::= STAR type
    /// ```
    pub fn parse_pointer_type(&mut self) -> ParseResult<AstPointerType> {
        let indirection = self.check(&TokenType::Star)?;
        let inner = self.parse_type()?;
        let node = AstPointerType {
            span: Span::from_pair(&indirection.span, inner.span()),
            inner: Box::new(inner),
        };
        Ok(node)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBinaryOp, AstBreakStmt, AstContinueStmt, AstExpr, AstIdentifier, AstType, AstUnaryOp,
    };
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::{InvalidIntegerLiteralError, ParseError, ParseResult};
    use eight_macros::{assert_err, assert_none, assert_ok, assert_some};
    use eight_span::Span;

    fn assert_parse<T>(
        input: &str,
        rule: impl FnOnce(&mut Parser) -> ParseResult<T>,
    ) -> ParseResult<T> {
        let mut lexer = Lexer::new(input);
        let mut p = Parser::new(&mut lexer);
        let production = rule(&mut p);
        assert_ok!(&production);
        let next = assert_ok!(p.lookahead());
        assert!(next.is_none(), "expected end of stream, got {:?}", next);
        production
    }

    #[test]
    fn test_parse_builtin_type() {
        let prod = assert_parse("i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Integer32(_)));

        let prod = assert_parse("unit", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Unit(_)));

        let prod = assert_parse("bool", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Boolean(_)));
    }

    #[test]
    fn test_parse_named_type() {
        let prod = assert_parse("Matrix", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert_eq!(prod.span(), &Span::new(0..6));
        assert!(matches!(prod, AstType::Named(inner) if inner.name.name == "Matrix"));
    }

    #[test]
    fn test_parse_pointer_type() {
        let prod = assert_parse("*i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Pointer(_)));
        if let AstType::Pointer(ptr) = prod {
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, AstType::Integer32(_)));
        }

        let prod = assert_parse("**i32", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Pointer(_)));
        if let AstType::Pointer(ptr) = prod {
            assert!(matches!(ptr.inner.as_ref(), AstType::Pointer(_)));
            let inner = ptr.inner.as_ref();
            if let AstType::Pointer(ptr) = inner {
                let inner = ptr.inner.as_ref();
                assert!(matches!(inner, AstType::Integer32(_)));
            }
        }

        let prod = assert_parse("*vec2", |p| p.parse_type());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstType::Pointer(_)));
        if let AstType::Pointer(ptr) = prod {
            assert!(matches!(*ptr.inner.as_ref(), AstType::Named(_)));
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, AstType::Named(name) if name.name.name == "vec2"));
        }
    }

    #[test]
    fn test_parse_type_member_item() {
        let prod = assert_parse("x: i32,", |p| p.parse_type_member_item());
        let prod = assert_ok!(prod);
        let name = prod.name;
        let ty = prod.ty;

        assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        assert!(matches!(&ty, AstType::Integer32(_)));

        let prod = assert_parse("x: *matrix,", |p| p.parse_type_member_item());
        let prod = assert_ok!(prod);
        let name = prod.name;
        let ty = prod.ty;

        assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        assert!(matches!(&ty, AstType::Pointer(_)));
        if let AstType::Pointer(ptr) = ty {
            assert!(matches!(*ptr.inner.as_ref(), AstType::Named(_)));
            let inner = ptr.inner.as_ref();
            assert!(matches!(inner, AstType::Named(name) if name.name.name == "matrix"));
        }
    }

    #[test]
    fn test_parse_type_item() {
        let prod = assert_parse("type Matrix = { x: i32, y: i32, }", |p| p.parse_type_item());
        let prod = assert_ok!(prod);
        let name = prod.name;
        let members = prod.members.as_slice();

        assert!(matches!(name, AstIdentifier { name, .. } if name == "Matrix"));
        assert_eq!(members.len(), 2);

        let prod = assert_parse("type Matrix = { x: i32, y: i32, z: *vec2, }", |p| {
            p.parse_type_item()
        });
        let prod = assert_ok!(prod);
        let name = prod.name;
        let members = prod.members.as_slice();

        assert!(matches!(name, AstIdentifier { name, .. } if name == "Matrix"));
        assert_eq!(members.len(), 3);
    }

    #[test]
    fn test_parse_fn_parameter_item() {
        let prod = assert_parse("x: i32", |p| p.parse_fn_parameter_item());
        let prod = assert_ok!(prod);

        let name = prod.name;
        let ty = prod.ty;

        assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        assert!(matches!(&ty, AstType::Integer32(_)));
    }

    #[test]
    fn test_parse_fn_item() {
        let prod = assert_parse("fn x(x: i32) -> i32 {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let name = prod.name;
        let parameters = prod.parameters.as_slice();
        let return_type = assert_some!(prod.return_type);
        let body = prod.body.as_slice();

        assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        assert_eq!(parameters.len(), 1);
        assert!(matches!(return_type, AstType::Integer32(_)));
        assert_eq!(body.len(), 0);

        let prod = assert_parse("fn zzz(y: *i32) {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let name = prod.name;
        let parameters = prod.parameters.as_slice();
        assert_none!(prod.return_type.as_ref());
        let body = prod.body.as_slice();

        assert!(matches!(name, AstIdentifier { name, .. } if name == "zzz"));
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

    #[test]
    fn test_parse_fn_item_with_type_parameters() {
        let prod = assert_parse("fn foo<T, U>() {}", |p| p.parse_fn_item());
        let prod = assert_ok!(prod);

        let type_parameters = prod.type_parameters.as_slice();
        assert_eq!(type_parameters.len(), 2);
    }

    #[test]
    fn test_parse_fn_type_parameter_item() {
        let prod = assert_parse("T", |p| p.parse_fn_type_parameter_item());
        let prod = assert_ok!(prod);
        let name = prod.name;
        assert!(matches!(name, AstIdentifier { name, .. } if name == "T"));
    }

    #[test]
    fn test_parse_intrinsic_fn_item() {
        let prod = assert_parse("intrinsic_fn foo(x: i32) -> i32;", |p| {
            p.parse_intrinsic_fn_item()
        });
        let prod = assert_ok!(prod);
        let name = prod.name;
        let parameters = prod.parameters.as_slice();
        let return_type = prod.return_type;
        assert_eq!(name.name, "foo");
        assert_eq!(parameters.len(), 1);
        assert!(matches!(return_type, AstType::Integer32(_)));
    }

    #[test]
    fn test_parse_intrinsic_fn_item_with_type_parameters() {
        let prod = assert_parse("intrinsic_fn malloc<T>() -> *T;", |p| {
            p.parse_intrinsic_fn_item()
        });
        let prod = assert_ok!(prod);
        let type_parameters = prod.type_parameters.as_slice();
        assert_eq!(type_parameters.len(), 1);
    }

    #[test]
    fn test_parse_intrinsic_scalar_item() {
        let prod = assert_parse("intrinsic_scalar i32;", |p| p.parse_intrinsic_scalar_item());
        let prod = assert_ok!(prod);
        let name = prod.name;
        assert!(matches!(name, AstIdentifier { name, .. } if name == "i32"));
    }

    #[test]
    fn test_parse_let_stmt() {
        let prod = assert_parse("let x = 1;", |p| p.parse_let_stmt());
        let prod = assert_ok!(prod);
        let name = prod.name;
        let initializer = prod.value;
        let ty = prod.ty.as_ref();
        assert_eq!(name.name, "x");
        assert!(matches!(initializer, AstExpr::IntegerLiteral(_)));
        assert_none!(ty);

        let prod = assert_parse("let x: i32 = 1;", |p| p.parse_let_stmt());
        let prod = assert_ok!(prod);
        let ty = prod.ty;
        let ty = assert_some!(ty);
        assert!(matches!(&ty, AstType::Integer32(_)));
    }

    #[test]
    fn test_parse_return_stmt() {
        let prod = assert_parse("return;", |p| p.parse_return_stmt());
        let prod = assert_ok!(prod);
        assert_none!(prod.value);

        let prod = assert_parse("return 1;", |p| p.parse_return_stmt());
        let prod = assert_ok!(prod);
        let value = assert_some!(prod.value);
        assert!(matches!(&value, AstExpr::IntegerLiteral(_)));
    }

    #[test]
    fn test_parse_for_stmt() {
        let prod = assert_parse("for (;;) {}", |p| p.parse_for_stmt());
        let prod = assert_ok!(prod);
        assert_none!(prod.initializer);
        assert_none!(prod.condition);
        assert_none!(prod.increment);
        let body = prod.body.as_slice();
        assert_eq!(body.len(), 0);

        let prod = assert_parse("for (let x = 1; x < 10; x = x + 1) { x; }", |p| {
            p.parse_for_stmt()
        });
        let prod = assert_ok!(prod);
        assert_some!(prod.initializer);
        assert_some!(prod.condition);
        assert_some!(prod.increment);
        let body = prod.body.as_slice();
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn test_parse_break_stmt() {
        let prod = assert_parse("break;", |p| p.parse_break_stmt());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstBreakStmt { .. }));
    }

    #[test]
    fn test_parse_continue_stmt() {
        let prod = assert_parse("continue;", |p| p.parse_continue_stmt());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstContinueStmt { .. }));
    }

    #[test]
    fn test_parse_if_stmt() {
        let prod = assert_parse("if (x) {}", |p| p.parse_if_stmt());
        let prod = assert_ok!(prod);
        let condition = prod.condition;
        let body = prod.happy_path.as_slice();
        assert!(matches!(condition, AstExpr::Reference(_)));
        if let AstExpr::Reference(condition) = condition {
            let name = condition.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        };
        assert_eq!(body.len(), 0);
        assert_none!(prod.unhappy_path);

        let prod = assert_parse("if (x) { y(); } else { z(); }", |p| p.parse_if_stmt());
        let prod = assert_ok!(prod);
        assert_some!(prod.unhappy_path);
    }

    #[test]
    fn test_parse_expr_stmt() {
        let prod = assert_parse("x;", |p| p.parse_expr_stmt());
        let prod = assert_ok!(prod);
        let expr = prod.expr;
        assert!(matches!(expr, AstExpr::Reference(_)));
        if let AstExpr::Reference(expr) = expr {
            let name = expr.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        };
    }

    #[test]
    fn test_parse_group_expr() {
        let prod = assert_parse("(x)", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Group(_)));
        if let AstExpr::Group(inner) = prod {
            let inner = inner.inner.as_ref();
            assert!(matches!(inner, AstExpr::Reference(_)));
        };
    }

    #[test]
    fn test_parse_reference_expr() {
        let prod = assert_parse("x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Reference(_)));
        if let AstExpr::Reference(inner) = prod {
            let name = inner.name;
            assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
        };

        let prod = assert_parse("  x  ", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert_eq!(prod.span(), &Span::new(2..3));
    }

    #[test]
    fn test_parse_literal_expr() {
        let prod = assert_parse("123", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::IntegerLiteral(_)));
        if let AstExpr::IntegerLiteral(inner) = prod {
            let value = inner.value;
            assert_eq!(value, 123);
        };

        let prod = assert_parse("true", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BooleanLiteral(_)));
        if let AstExpr::BooleanLiteral(inner) = prod {
            let value = inner.value;
            assert!(value);
        };

        let prod = assert_parse("false", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BooleanLiteral(_)));
        if let AstExpr::BooleanLiteral(inner) = prod {
            let value = inner.value;
            assert!(!value);
        };
    }

    #[test]
    fn test_parse_dot_index_expr() {
        let prod = assert_parse("x.y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::DotIndex(_)));
        if let AstExpr::DotIndex(inner) = prod {
            let origin = inner.origin.as_ref();
            assert!(matches!(origin, AstExpr::Reference(_)));
            if let AstExpr::Reference(origin) = origin {
                let name = &origin.name;
                assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            };
            let index = inner.index;
            assert!(matches!(index, AstIdentifier { name, .. } if name == "y"));
        };
    }

    #[test]
    fn test_parse_bracket_index_expr() {
        let prod = assert_parse("x[y]", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BracketIndex(_)));
        if let AstExpr::BracketIndex(inner) = prod {
            let origin = inner.origin.as_ref();
            assert!(matches!(origin, AstExpr::Reference(_)));
            if let AstExpr::Reference(origin) = origin {
                let name = &origin.name;
                assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            };
            let index = inner.index.as_ref();
            assert!(matches!(index, AstExpr::Reference(_)));
            if let AstExpr::Reference(index) = index {
                let name = &index.name;
                assert!(matches!(name, AstIdentifier { name, .. } if name == "y"));
            };
        };
    }

    #[test]
    fn test_parse_call_expr() {
        let prod = assert_parse("x()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert_eq!(prod.span(), &Span::new(0..3));
        assert!(matches!(&prod, AstExpr::Call(_)));
        if let AstExpr::Call(inner) = prod {
            let origin = inner.callee.as_ref();
            let count = inner.arguments.len();
            assert_eq!(count, 0);
            assert!(matches!(origin, AstExpr::Reference(_)));
            if let AstExpr::Reference(origin) = origin {
                let name = &origin.name;
                assert!(matches!(name, AstIdentifier { name, .. } if name == "x"));
            };
        };

        let prod = assert_parse("x(z)", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Call(_)));
        if let AstExpr::Call(inner) = prod {
            let count = inner.arguments.len();
            assert_eq!(count, 1);
        }

        let prod = assert_parse("x(z, foo(bar, baz()))", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert_eq!(prod.span(), &Span::new(0..21));
        assert!(matches!(&prod, AstExpr::Call(_)));
        if let AstExpr::Call(inner) = prod {
            let count = inner.arguments.len();
            assert_eq!(count, 2);
        }
    }

    #[test]
    fn test_parse_call_expr_with_type_arguments() {
        let prod = assert_parse("x::<i32, bool>()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Call(_)));
        if let AstExpr::Call(inner) = prod {
            let count = inner.type_arguments.len();
            assert_eq!(count, 2);
            assert!(matches!(&inner.type_arguments[0], AstType::Integer32(_)));
            assert!(matches!(&inner.type_arguments[1], AstType::Boolean(_)));
        }
    }

    #[test]
    fn test_parse_call_expr_with_turbo_fish_zero_types() {
        let prod = assert_parse("x::<>()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Call(_)));
        if let AstExpr::Call(inner) = prod {
            let count = inner.type_arguments.len();
            assert_eq!(count, 0);
        }
    }

    #[test]
    fn test_parse_construct_expr() {
        let prod = assert_parse("new x {}", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Construct(_)));
        if let AstExpr::Construct(inner) = prod {
            let count = inner.arguments.len();
            assert_eq!(count, 0);
        };

        let prod = assert_parse("new x { y: z }", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Construct(_)));
        if let AstExpr::Construct(inner) = prod {
            let count = inner.arguments.len();
            assert_eq!(count, 1);
        }

        let prod = assert_parse("new x { y: notrailingcomma }", |p| p.parse_expr());
        assert_ok!(prod);
    }

    #[test]
    fn test_parse_constructor_grammar_allows_non_id_types() {
        let prod = assert_parse("new *x {}", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Construct(_)));
    }

    #[test]
    fn test_parse_unary_expr() {
        let prod = assert_parse("-x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::UnaryOp(_)));
        if let AstExpr::UnaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstUnaryOp::Neg);
        };

        let prod = assert_parse("*x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::UnaryOp(_)));
        if let AstExpr::UnaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstUnaryOp::Deref);
        };

        let prod = assert_parse("&x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::UnaryOp(_)));
        if let AstExpr::UnaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstUnaryOp::AddressOf);
        };
    }

    #[test]
    fn test_parse_multiplicative_expr() {
        let prod = assert_parse("x + y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Add);
        };

        let prod = assert_parse("x * y / z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Mul);
        };
    }

    #[test]
    fn test_parse_additive_expr() {
        let prod = assert_parse("x - y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Sub);
        };

        let prod = assert_parse("x + y * z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            let rhs = inner.rhs.as_ref();
            assert_eq!(op, &AstBinaryOp::Add);

            assert!(matches!(rhs, AstExpr::BinaryOp(_)));
            if let AstExpr::BinaryOp(inner) = rhs {
                let op = &inner.op;
                assert_eq!(op, &AstBinaryOp::Mul);
            };
        };
    }

    #[test]
    fn test_parse_comparison_expr() {
        let prod = assert_parse("x < y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Lt);
        };

        let prod = assert_parse("x < y < z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::BinaryOp(_)));
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Lt);

            let rhs = inner.rhs.as_ref();
            assert!(matches!(rhs, AstExpr::BinaryOp(_)));
            if let AstExpr::BinaryOp(inner) = rhs {
                let op = &inner.op;
                assert_eq!(op, &AstBinaryOp::Lt);
            };
        };
    }

    #[test]
    fn test_parse_logical_and_expr() {
        let prod = assert_parse("a + 3 && y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::And);
        };
    }

    #[test]
    fn test_parse_logical_or_expr() {
        let prod = assert_parse("a || y()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        if let AstExpr::BinaryOp(inner) = prod {
            let op = &inner.op;
            assert_eq!(op, &AstBinaryOp::Or);
        };
    }

    #[test]
    fn test_parse_assign_expr() {
        let prod = assert_parse("a = 3", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(&prod, AstExpr::Assign(_)));
    }

    #[test]
    fn test_parse_invalid_literal() {
        let mut lexer = Lexer::new("let k = 1234773457276345671237572345;");
        let mut parser = Parser::new(&mut lexer);
        let prod = assert_err!(parser.parse_let_stmt());
        assert!(
            matches!(prod, ParseError::InvalidIntegerLiteral(InvalidIntegerLiteralError {
            span, ..
        }) if span.low == 8 && span.high == 36)
        );
    }
}
