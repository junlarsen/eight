use crate::ast::{
    AssignExpr, BinaryOp, BinaryOpExpr, BracketIndexExpr, BreakStmt, CallExpr, ConstructExpr,
    ConstructorExprArgument, ContinueStmt, DotIndexExpr, Expr, ExprStmt, ForStmt,
    ForStmtInitializer, FunctionItem, FunctionParameterItem, GroupExpr, Identifier, IfStmt,
    Integer32Type, IntegerLiteralExpr, Item, LetStmt, NamedType, PointerType, ReferenceExpr,
    ReturnStmt, Stmt, TranslationUnit, Type, TypeItem, TypeMemberItem, UnaryOp, UnaryOpExpr,
    UnitType,
};
use crate::lexer::Lexer;
use crate::{
    ParseError, ParseResult, Span, Token, TokenType, UnexpectedEndOfInputError,
    UnexpectedTokenError,
};

pub struct Parser<'a> {
    input: ParserInput<'a>,
}

pub struct ParserInput<'a> {
    lexer: Lexer<'a>,
    /// Buffer for the next token lookahead.
    ///
    /// If the parser for any reason needs more than LL(1) in the future, this can be replaced with
    /// a stack of tokens.
    la: Option<Token>,
}

impl<'a> ParserInput<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer, la: None }
    }

    pub fn lookahead(&mut self) -> ParseResult<Option<&Token>> {
        if self.la.is_none() {
            self.la = match self.lexer.produce() {
                Ok(tok) => Some(tok),
                Err(ParseError::UnexpectedEndOfInput(_)) => None,
                Err(err) => return Err(err),
            };
        }
        Ok(self.la.as_ref())
    }

    pub fn eat(&mut self) -> ParseResult<Token> {
        if let Some(token) = self.la.take() {
            return Ok(token);
        }
        self.lexer.produce()
    }
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
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

    pub fn lookahead_or_err(&mut self) -> ParseResult<&Token> {
        let span = Span::pos(self.input.lexer.pos());
        self.input
            .lookahead()?
            .ok_or(ParseError::UnexpectedEndOfInput(
                UnexpectedEndOfInputError { span },
            ))
    }

    /// Determine if the next token in the token stream matches the given type.
    pub fn lookahead_check(&mut self, ty: TokenType) -> ParseResult<bool> {
        let token = self.lookahead()?;
        match token {
            Some(token) if token.ty == ty => Ok(true),
            _ => Ok(false),
        }
    }

    /// Consume the next token from the token stream and ensure it matches the given type.
    ///
    /// If the token doesn't match, the entire parser fails.
    pub fn check(&mut self, ty: TokenType) -> ParseResult<Token> {
        let token = self.eat()?;
        match token {
            token if token.ty == ty => Ok(token),
            _ => Err(ParseError::UnexpectedToken(UnexpectedTokenError {
                span: token.span.clone(),
                token,
            })),
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
        while self.lookahead()?.is_some() {
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
        let token = self.lookahead_or_err()?;
        match token.ty {
            TokenType::KeywordFn => self.parse_fn_item().map(|v| Box::new(Item::Function(v))),
            TokenType::KeywordType => self.parse_type_item().map(|v| Box::new(Item::Type(v))),
            _ => {
                let token = self.eat()?;
                Err(ParseError::UnexpectedToken(UnexpectedTokenError {
                    span: token.span.clone(),
                    token,
                }))
            }
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
        let start = self.check(TokenType::KeywordFn)?;
        let id = self.parse_identifier()?;
        self.check(TokenType::OpenParen)?;
        let mut parameters = Vec::new();
        while !self.lookahead_check(TokenType::CloseParen)? {
            let parameter = self.parse_fn_parameter_item()?;
            // Consume commas if we're not matching the end of the parameter list.
            if !self.lookahead_check(TokenType::CloseParen)? {
                self.check(TokenType::Comma)?;
            }
            parameters.push(parameter);
        }
        self.check(TokenType::CloseParen)?;
        let return_type = if self.lookahead_check(TokenType::Arrow)? {
            self.check(TokenType::Arrow)?;
            Some(self.parse_type()?)
        } else {
            None
        };

        self.check(TokenType::OpenBrace)?;
        let mut body = Vec::new();
        while !self.lookahead_check(TokenType::CloseBrace)? {
            body.push(self.parse_stmt()?);
        }
        let end = self.check(TokenType::CloseBrace)?;

        Ok(Box::new(FunctionItem {
            span: Span::from_pair(&start.span, &end.span),
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
        self.check(TokenType::Colon)?;
        let ty = self.parse_type()?;
        Ok(Box::new(FunctionParameterItem {
            span: Span::from_pair(&id.span, ty.span()),
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
        let start = self.check(TokenType::KeywordType)?;
        let id = self.parse_identifier()?;
        self.check(TokenType::Equal)?;
        self.check(TokenType::OpenBrace)?;
        let mut members = Vec::new();
        while !self.lookahead_check(TokenType::CloseBrace)? {
            members.push(self.parse_type_member_item()?);
        }
        let end = self.check(TokenType::CloseBrace)?;
        Ok(Box::new(TypeItem {
            span: Span::from_pair(&start.span, &end.span),
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
        self.check(TokenType::Colon)?;
        let ty = self.parse_type()?;
        let end = self.check(TokenType::Comma)?;
        Ok(Box::new(TypeMemberItem {
            span: Span::from_pair(&id.span, &end.span),
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
        let next = self.lookahead_or_err()?;
        match next.ty {
            TokenType::KeywordLet => self.parse_let_stmt().map(|v| Box::new(Stmt::Let(v))),
            TokenType::KeywordReturn => self.parse_return_stmt().map(|v| Box::new(Stmt::Return(v))),
            TokenType::KeywordFor => self.parse_for_stmt().map(|v| Box::new(Stmt::For(v))),
            TokenType::KeywordBreak => self.parse_break_stmt().map(|v| Box::new(Stmt::Break(v))),
            TokenType::KeywordContinue => self
                .parse_continue_stmt()
                .map(|v| Box::new(Stmt::Continue(v))),
            TokenType::KeywordIf => self.parse_if_stmt().map(|v| Box::new(Stmt::If(v))),
            _ => self.parse_expr_stmt().map(|v| Box::new(Stmt::Expr(v))),
        }
    }

    /// Parse a let statement.
    ///
    /// ```text
    /// let_stmt ::= KEYWORD_LET IDENTIFIER (COLON type)? EQUAL expr SEMICOLON
    /// ```
    pub fn parse_let_stmt(&mut self) -> ParseResult<Box<LetStmt>> {
        let start = self.check(TokenType::KeywordLet)?;
        let id = self.parse_identifier()?;
        let ty = if self.lookahead_check(TokenType::Colon)? {
            self.check(TokenType::Colon)?;
            Some(self.parse_type()?)
        } else {
            None
        };
        self.check(TokenType::Equal)?;
        let expr = self.parse_expr()?;
        let end = self.check(TokenType::Semicolon)?;

        Ok(Box::new(LetStmt {
            span: Span::from_pair(&start.span, &end.span),
            name: id,
            r#type: ty,
            value: expr,
        }))
    }

    /// Parses a return statement.
    ///
    /// ```text
    /// return_stmt ::= RETURN expr? SEMICOLON
    /// ```
    pub fn parse_return_stmt(&mut self) -> ParseResult<Box<ReturnStmt>> {
        let start = self.check(TokenType::KeywordReturn)?;
        let value = if !self.lookahead_check(TokenType::Semicolon)? {
            Some(self.parse_expr()?)
        } else {
            None
        };
        let end = self.check(TokenType::Semicolon)?;
        Ok(Box::new(ReturnStmt {
            span: Span::from_pair(&start.span, &end.span),
            value,
        }))
    }

    /// Parses a for statement.
    ///
    /// ```text
    /// for_stmt ::= FOR LPAREN for_stmt_initializer? SEMICOLON expr? SEMICOLON expr? RPAREN LBRACE stmt* RBRACE
    /// ```
    pub fn parse_for_stmt(&mut self) -> ParseResult<Box<ForStmt>> {
        let start = self.check(TokenType::KeywordFor)?;
        self.check(TokenType::OpenParen)?;
        let initializer = if !self.lookahead_check(TokenType::Semicolon)? {
            Some(self.parse_for_stmt_initializer()?)
        } else {
            None
        };
        self.check(TokenType::Semicolon)?;
        let condition = if !self.lookahead_check(TokenType::Semicolon)? {
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.check(TokenType::Semicolon)?;
        let increment = if !self.lookahead_check(TokenType::CloseParen)? {
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.check(TokenType::CloseParen)?;
        self.check(TokenType::OpenBrace)?;
        let mut body = Vec::new();
        while !self.lookahead_check(TokenType::CloseBrace)? {
            body.push(self.parse_stmt()?);
        }
        let end = self.check(TokenType::CloseBrace)?;
        Ok(Box::new(ForStmt {
            span: Span::from_pair(&start.span, &end.span),
            initializer,
            condition,
            increment,
            body,
        }))
    }

    /// Parses a for statement initializer.
    ///
    /// ```text
    /// for_stmt_initializer ::= LET identifier EQUAL expr
    /// ```
    pub fn parse_for_stmt_initializer(&mut self) -> ParseResult<Box<ForStmtInitializer>> {
        let start = self.check(TokenType::KeywordLet)?;
        let name = self.parse_identifier()?;
        self.check(TokenType::Equal)?;
        let initializer = self.parse_expr()?;
        Ok(Box::new(ForStmtInitializer {
            span: Span::from_pair(&start.span, initializer.span()),
            name,
            initializer,
        }))
    }

    /// Parses a break statement.
    ///
    /// ```text
    /// break_stmt ::= BREAK SEMICOLON
    /// ```
    pub fn parse_break_stmt(&mut self) -> ParseResult<Box<BreakStmt>> {
        let start = self.check(TokenType::KeywordBreak)?;
        let end = self.check(TokenType::Semicolon)?;
        Ok(Box::new(BreakStmt {
            span: Span::from_pair(&start.span, &end.span),
        }))
    }

    /// Parses a continue statement.
    ///
    /// ```text
    /// continue_stmt ::= CONTINUE SEMICOLON
    /// ```
    pub fn parse_continue_stmt(&mut self) -> ParseResult<Box<ContinueStmt>> {
        let start = self.check(TokenType::KeywordContinue)?;
        let end = self.check(TokenType::Semicolon)?;
        Ok(Box::new(ContinueStmt {
            span: Span::from_pair(&start.span, &end.span),
        }))
    }

    /// Parses an if statement.
    ///
    /// ```text
    /// if_stmt ::= IF LPAREN expr RPAREN LBRACE stmt* RBRACE (ELSE LBRACE stmt* RBRACE)?
    pub fn parse_if_stmt(&mut self) -> ParseResult<Box<IfStmt>> {
        let start = self.check(TokenType::KeywordIf)?;
        self.check(TokenType::OpenParen)?;
        let condition = self.parse_expr()?;
        self.check(TokenType::CloseParen)?;
        self.check(TokenType::OpenBrace)?;
        let mut body = Vec::new();
        while !self.lookahead_check(TokenType::CloseBrace)? {
            body.push(self.parse_stmt()?);
        }
        // We default to the end of the if statement by its closing brace if it doesn't have an else
        // block attached. Otherwise, we use the end of the else block.
        let mut end = self.check(TokenType::CloseBrace)?;
        let r#else = if self.lookahead_check(TokenType::KeywordElse)? {
            self.check(TokenType::KeywordElse)?;
            self.check(TokenType::OpenBrace)?;
            let mut r#else = Vec::new();
            while !self.lookahead_check(TokenType::CloseBrace)? {
                r#else.push(self.parse_stmt()?);
            }
            end = self.check(TokenType::CloseBrace)?;
            Some(r#else)
        } else {
            None
        };
        Ok(Box::new(IfStmt {
            span: Span::from_pair(&start.span, &end.span),
            condition,
            happy_path: body,
            unhappy_path: r#else,
        }))
    }

    /// Parses an expression statement.
    ///
    /// ```text
    /// expr_stmt ::= expr SEMICOLON
    pub fn parse_expr_stmt(&mut self) -> ParseResult<Box<ExprStmt>> {
        let expr = self.parse_expr()?;
        let end = self.check(TokenType::Semicolon)?;
        Ok(Box::new(ExprStmt {
            span: Span::from_pair(expr.span(), &end.span),
            expr,
        }))
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
    pub fn parse_expr(&mut self) -> ParseResult<Box<Expr>> {
        self.parse_assign_expr()
    }

    /// Parse an assignment expression.
    ///
    /// ```text
    /// assign_expr ::= logical_expr EQUAL assign_expr
    /// ```
    pub fn parse_assign_expr(&mut self) -> ParseResult<Box<Expr>> {
        let expr = self.parse_logical_or_expr()?;

        if self.lookahead_check(TokenType::Equal)? {
            self.check(TokenType::Equal)?;
            let rhs = self.parse_assign_expr()?;
            return Ok(Box::new(Expr::Assign(Box::new(AssignExpr {
                span: Span::from_pair(expr.span(), rhs.span()),
                lhs: expr,
                rhs,
            }))));
        };

        Ok(expr)
    }

    /// Parse a logical or expression.
    ///
    /// ```text
    /// logical_or_expr ::= logical_and_expr (OR logical_and_expr)*
    /// ```
    pub fn parse_logical_or_expr(&mut self) -> ParseResult<Box<Expr>> {
        let lhs = self.parse_logical_and_expr()?;

        if self.lookahead_check(TokenType::LogicalOr)? {
            self.check(TokenType::LogicalOr)?;
            let rhs = self.parse_logical_or_expr()?;
            return Ok(Box::new(Expr::BinaryOp(Box::new(BinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs,
                rhs,
                op: BinaryOp::Or,
            }))));
        };

        Ok(lhs)
    }

    /// Parse a logical and expression.
    ///
    /// ```text
    /// logical_and_expr ::= comparison_expr (AND comparison_expr)*
    /// ```
    pub fn parse_logical_and_expr(&mut self) -> ParseResult<Box<Expr>> {
        let lhs = self.parse_comparison_expr()?;

        if self.lookahead_check(TokenType::LogicalAnd)? {
            self.check(TokenType::LogicalAnd)?;
            let rhs = self.parse_logical_and_expr()?;
            return Ok(Box::new(Expr::BinaryOp(Box::new(BinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs,
                rhs,
                op: BinaryOp::And,
            }))));
        };

        Ok(lhs)
    }

    /// Parse a comparison expression.
    ///
    /// ```text
    /// comparison_expr ::= additive_expr (comparison_op additive_expr)*
    /// comparison_op ::= EQUAL_EQUAL | BANG_EQUAL | LESS_THAN | GREATER_THAN | LESS_THAN_EQUAL | GREATER_THAN_EQUAL
    /// ```
    pub fn parse_comparison_expr(&mut self) -> ParseResult<Box<Expr>> {
        let lhs = self.parse_additive_expr()?;
        let is_next_comparison = self.lookahead_check(TokenType::EqualEqual)?
            || self.lookahead_check(TokenType::BangEqual)?
            || self.lookahead_check(TokenType::OpenAngle)?
            || self.lookahead_check(TokenType::CloseAngle)?
            || self.lookahead_check(TokenType::LessThanEqual)?
            || self.lookahead_check(TokenType::GreaterThanEqual)?;

        if is_next_comparison {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::EqualEqual => BinaryOp::Eq,
                TokenType::BangEqual => BinaryOp::Neq,
                TokenType::OpenAngle => BinaryOp::Lt,
                TokenType::CloseAngle => BinaryOp::Gt,
                TokenType::LessThanEqual => BinaryOp::Lte,
                TokenType::GreaterThanEqual => BinaryOp::Gte,
                _ => unreachable!(),
            };
            let rhs = self.parse_comparison_expr()?;
            return Ok(Box::new(Expr::BinaryOp(Box::new(BinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs,
                rhs,
                op,
            }))));
        }

        Ok(lhs)
    }

    /// Parse an additive expression.
    ///
    /// ```text
    /// additive_expr ::= multiplicative_expr (additive_op multiplicative_expr)*
    /// additive_op ::= PLUS | MINUS
    /// ```
    pub fn parse_additive_expr(&mut self) -> ParseResult<Box<Expr>> {
        let lhs = self.parse_multiplicative_expr()?;
        let is_next_additive =
            self.lookahead_check(TokenType::Plus)? || self.lookahead_check(TokenType::Minus)?;

        if is_next_additive {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::Plus => BinaryOp::Add,
                TokenType::Minus => BinaryOp::Sub,
                _ => unreachable!(),
            };
            let rhs = self.parse_additive_expr()?;
            return Ok(Box::new(Expr::BinaryOp(Box::new(BinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs,
                rhs,
                op,
            }))));
        }

        Ok(lhs)
    }

    /// Parse a multiplicative expression.
    ///
    /// ```text
    /// multiplicative_expr ::= unary_expr (multiplicative_op unary_expr)*
    /// multiplicative_op ::= STAR | SLASH | PERCENT
    /// ```
    pub fn parse_multiplicative_expr(&mut self) -> ParseResult<Box<Expr>> {
        let lhs = self.parse_unary_expr()?;
        let is_next_multiplicative = self.lookahead_check(TokenType::Star)?
            || self.lookahead_check(TokenType::Slash)?
            || self.lookahead_check(TokenType::Percent)?;

        if is_next_multiplicative {
            let tok = self.eat()?;
            let op = match &tok.ty {
                TokenType::Star => BinaryOp::Mul,
                TokenType::Slash => BinaryOp::Div,
                TokenType::Percent => BinaryOp::Rem,
                _ => unreachable!(),
            };
            let rhs = self.parse_multiplicative_expr()?;
            return Ok(Box::new(Expr::BinaryOp(Box::new(BinaryOpExpr {
                span: Span::from_pair(lhs.span(), rhs.span()),
                lhs,
                rhs,
                op,
            }))));
        }

        Ok(lhs)
    }

    /// Parse an unary expression.
    ///
    /// ```text
    /// unary_expr ::= unary_op unary_expr | group_expr
    /// unary_op ::= MINUS | BANG | DEREF | STAR
    /// ```
    pub fn parse_unary_expr(&mut self) -> ParseResult<Box<Expr>> {
        let token = self.lookahead_or_err()?;
        match token.ty {
            TokenType::Minus => {
                let op = self.check(TokenType::Minus)?;
                let rhs = self.parse_unary_expr()?;
                Ok(Box::new(Expr::UnaryOp(Box::new(UnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    op: UnaryOp::Neg,
                    operand: rhs,
                }))))
            }
            TokenType::Bang => {
                let op = self.check(TokenType::Bang)?;
                let rhs = self.parse_unary_expr()?;
                Ok(Box::new(Expr::UnaryOp(Box::new(UnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    op: UnaryOp::Not,
                    operand: rhs,
                }))))
            }
            TokenType::Star => {
                let op = self.check(TokenType::Star)?;
                let rhs = self.parse_unary_expr()?;
                Ok(Box::new(Expr::UnaryOp(Box::new(UnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    op: UnaryOp::Deref,
                    operand: rhs,
                }))))
            }
            TokenType::AddressOf => {
                let op = self.check(TokenType::AddressOf)?;
                let rhs = self.parse_unary_expr()?;
                Ok(Box::new(Expr::UnaryOp(Box::new(UnaryOpExpr {
                    span: Span::from_pair(&op.span, rhs.span()),
                    op: UnaryOp::AddressOf,
                    operand: rhs,
                }))))
            }
            _ => self.parse_call_expr(),
        }
    }

    /// Parse a call expression.
    ///
    /// ```text
    /// call_expr ::= construct_expr (OPEN_PAREN (expr (COMMA expr)*)? CLOSE_PAREN)?
    /// ```
    pub fn parse_call_expr(&mut self) -> ParseResult<Box<Expr>> {
        let callee = self.parse_construct_expr()?;
        if self.lookahead_check(TokenType::OpenParen)? {
            self.check(TokenType::OpenParen)?;
            let mut arguments = Vec::new();
            while !self.lookahead_check(TokenType::CloseParen)? {
                arguments.push(self.parse_expr()?);
                if !self.lookahead_check(TokenType::CloseParen)? {
                    self.check(TokenType::Comma)?;
                }
            }
            let end = self.check(TokenType::CloseParen)?;
            return Ok(Box::new(Expr::Call(Box::new(CallExpr {
                span: Span::from_pair(callee.span(), &end.span),
                callee,
                arguments,
            }))));
        };

        Ok(callee)
    }

    /// Parse a construct expression.
    ///
    /// ```text
    /// construct_expr ::= parse_dot_index_expr OPEN_BRACE (construct_expr_argument (COMMA construct_expr_argument)*)? CLOSE_BRACE
    /// ```
    pub fn parse_construct_expr(&mut self) -> ParseResult<Box<Expr>> {
        let callee = self.parse_bracket_index_expr()?;

        if self.lookahead_check(TokenType::OpenBrace)? {
            self.check(TokenType::OpenBrace)?;
            let mut arguments = Vec::new();
            while !self.lookahead_check(TokenType::CloseBrace)? {
                arguments.push(self.parse_construct_expr_argument()?);
                if !self.lookahead_check(TokenType::CloseBrace)? {
                    self.check(TokenType::Comma)?;
                }
            }
            let end = self.check(TokenType::CloseBrace)?;
            return Ok(Box::new(Expr::Construct(Box::new(ConstructExpr {
                span: Span::from_pair(callee.span(), &end.span),
                callee,
                arguments,
            }))));
        };

        Ok(callee)
    }

    /// Parse a construct expression argument.
    ///
    /// ```text
    /// construct_expr_argument ::= identifier COLON expr
    pub fn parse_construct_expr_argument(&mut self) -> ParseResult<Box<ConstructorExprArgument>> {
        let id = self.parse_identifier()?;
        self.check(TokenType::Colon)?;
        let expr = self.parse_expr()?;
        Ok(Box::new(ConstructorExprArgument {
            span: Span::from_pair(&id.span, expr.span()),
            field: id,
            expr,
        }))
    }

    /// Parse a bracket index expression.
    ///
    /// ```text
    /// bracket_index_expr ::= reference_expr OPEN_BRACKET expr CLOSE_BRACKET
    /// ```
    pub fn parse_bracket_index_expr(&mut self) -> ParseResult<Box<Expr>> {
        let origin = self.parse_dot_index_expr()?;
        if self.lookahead_check(TokenType::OpenBracket)? {
            self.check(TokenType::OpenBracket)?;
            let index = self.parse_expr()?;
            let end = self.check(TokenType::CloseBracket)?;
            return Ok(Box::new(Expr::BracketIndex(Box::new(BracketIndexExpr {
                span: Span::from_pair(origin.span(), &end.span),
                origin,
                index,
            }))));
        }
        Ok(origin)
    }

    /// Parse a dot index expression.
    ///
    /// ```text
    /// dot_index_expr ::= reference_expr DOT identifier
    /// ```
    pub fn parse_dot_index_expr(&mut self) -> ParseResult<Box<Expr>> {
        let origin = self.parse_reference_expr()?;
        if self.lookahead_check(TokenType::Dot)? {
            self.check(TokenType::Dot)?;
            let index = self.parse_identifier()?;
            return Ok(Box::new(Expr::DotIndex(Box::new(DotIndexExpr {
                span: Span::from_pair(origin.span(), &index.span),
                origin,
                index,
            }))));
        }
        Ok(origin)
    }

    /// Parse a reference expression.
    ///
    /// ```text
    /// reference_expr ::= identifier | group_expr
    /// ```
    pub fn parse_reference_expr(&mut self) -> ParseResult<Box<Expr>> {
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
            return Ok(Box::new(Expr::Reference(Box::new(ReferenceExpr {
                span: id.span.clone(),
                name: id,
            }))));
        }
        self.parse_literal_expr()
    }

    /// Parse an integer literal expression.
    ///
    /// ```text
    /// integer_literal_expr ::= INTEGER_LITERAL
    /// ```
    pub fn parse_literal_expr(&mut self) -> ParseResult<Box<Expr>> {
        if matches!(
            self.lookahead()?,
            Some(Token {
                ty: TokenType::IntegerLiteral(_),
                ..
            })
        ) {
            let token = self.eat()?;
            let value = match token.ty {
                TokenType::IntegerLiteral(v) => v,
                _ => unreachable!("the type should have been checked before to be safe to unwrap"),
            };
            return Ok(Box::new(Expr::IntegerLiteral(Box::new(
                IntegerLiteralExpr {
                    span: token.span,
                    value,
                },
            ))));
        }

        self.parse_group_expr()
    }

    /// Parse a group expression.
    ///
    /// ```text
    /// group_expr ::= OPEN_PAREN expr CLOSE_PAREN
    /// ```
    pub fn parse_group_expr(&mut self) -> ParseResult<Box<Expr>> {
        if self.lookahead_check(TokenType::OpenParen)? {
            let start = self.check(TokenType::OpenParen)?;
            let inner = self.parse_expr()?;
            let end = self.check(TokenType::CloseParen)?;
            return Ok(Box::new(Expr::Group(Box::new(GroupExpr {
                span: Span::from_pair(&start.span, &end.span),
                inner,
            }))));
        };
        let token = self.eat()?;
        Err(ParseError::UnexpectedToken(UnexpectedTokenError {
            span: token.span.clone(),
            token,
        }))
    }

    /// Parse an identifier.
    ///
    /// ```text
    /// identifier ::= IDENTIFIER
    /// ```
    pub fn parse_identifier(&mut self) -> ParseResult<Box<Identifier>> {
        let token = self.eat()?;
        match token {
            Token {
                ty: TokenType::Identifier(id),
                span,
            } => Ok(Box::new(Identifier { name: id, span })),
            _ => Err(ParseError::from(UnexpectedTokenError {
                span: token.span.clone(),
                token,
            })),
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
        let token = self.lookahead_or_err()?;
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
            _ => {
                let token = self.eat()?;
                Err(ParseError::from(UnexpectedTokenError {
                    span: token.span.clone(),
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
        let indirection = self.check(TokenType::Star)?;
        let inner = self.parse_type()?;
        Ok(Box::new(PointerType {
            span: Span::from_pair(&indirection.span, inner.span()),
            inner,
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{BinaryOp, BreakStmt, ContinueStmt, Expr, Identifier, Type, UnaryOp};
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::{InvalidIntegerLiteralError, ParseError, ParseResult};
    use hachi_macros::{assert_err, assert_none, assert_ok, assert_some};

    fn assert_parse<T>(
        input: &str,
        rule: impl FnOnce(&mut Parser) -> ParseResult<T>,
    ) -> ParseResult<T> {
        let mut p = Parser::new(Lexer::new(input));
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
        if let Type::Pointer(ptr) = r#type {
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

    #[test]
    fn test_parse_let_stmt() {
        let prod = assert_parse("let x = 1;", |p| p.parse_let_stmt());
        let prod = assert_ok!(prod);
        let name = prod.name.as_ref();
        let initializer = prod.value.as_ref();
        let r#type = prod.r#type.as_ref();
        assert_eq!(name.name, "x");
        assert!(matches!(initializer, Expr::IntegerLiteral(_)));
        assert_none!(r#type);

        let prod = assert_parse("let x: i32 = 1;", |p| p.parse_let_stmt());
        let prod = assert_ok!(prod);
        let r#type = prod.r#type;
        let r#type = assert_some!(r#type);
        assert!(matches!(*r#type, Type::Integer32(_)));
    }

    #[test]
    fn test_parse_return_stmt() {
        let prod = assert_parse("return;", |p| p.parse_return_stmt());
        let prod = assert_ok!(prod);
        assert_none!(prod.value);

        let prod = assert_parse("return 1;", |p| p.parse_return_stmt());
        let prod = assert_ok!(prod);
        let value = assert_some!(prod.value);
        assert!(matches!(*value, Expr::IntegerLiteral(_)));
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
        assert!(matches!(*prod, BreakStmt { .. }));
    }

    #[test]
    fn test_parse_continue_stmt() {
        let prod = assert_parse("continue;", |p| p.parse_continue_stmt());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, ContinueStmt { .. }));
    }

    #[test]
    fn test_parse_if_stmt() {
        let prod = assert_parse("if (x) {}", |p| p.parse_if_stmt());
        let prod = assert_ok!(prod);
        let condition = prod.condition.as_ref();
        let body = prod.happy_path.as_slice();
        assert!(matches!(condition, Expr::Reference(_)));
        if let Expr::Reference(condition) = condition {
            let name = condition.as_ref().name.as_ref();
            assert!(matches!(name, Identifier { name, .. } if name == "x"));
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
        let expr = prod.expr.as_ref();
        assert!(matches!(expr, Expr::Reference(_)));
        if let Expr::Reference(expr) = expr {
            let name = expr.as_ref().name.as_ref();
            assert!(matches!(name, Identifier { name, .. } if name == "x"));
        };
    }

    #[test]
    fn test_parse_group_expr() {
        let prod = assert_parse("(x)", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Group(_)));
        if let Expr::Group(inner) = *prod {
            let inner = inner.as_ref().inner.as_ref();
            assert!(matches!(inner, Expr::Reference(_)));
        };
    }

    #[test]
    fn test_parse_reference_expr() {
        let prod = assert_parse("x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Reference(_)));
        if let Expr::Reference(inner) = *prod {
            let name = inner.as_ref().name.as_ref();
            assert!(matches!(name, Identifier { name, .. } if name == "x"));
        };
    }

    #[test]
    fn test_parse_literal_expr() {
        let prod = assert_parse("123", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::IntegerLiteral(_)));
        if let Expr::IntegerLiteral(inner) = *prod {
            let value = inner.as_ref().value;
            assert_eq!(value, 123);
        };
    }

    #[test]
    fn test_parse_dot_index_expr() {
        let prod = assert_parse("x.y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::DotIndex(_)));
        if let Expr::DotIndex(inner) = *prod {
            let origin = inner.as_ref().origin.as_ref();
            assert!(matches!(origin, Expr::Reference(_)));
            if let Expr::Reference(origin) = origin {
                let name = origin.as_ref().name.as_ref();
                assert!(matches!(name, Identifier { name, .. } if name == "x"));
            };
            let index = inner.as_ref().index.as_ref();
            assert!(matches!(index, Identifier { name, .. } if name == "y"));
        };
    }

    #[test]
    fn test_parse_bracket_index_expr() {
        let prod = assert_parse("x[y]", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BracketIndex(_)));
        if let Expr::BracketIndex(inner) = *prod {
            let origin = inner.as_ref().origin.as_ref();
            assert!(matches!(origin, Expr::Reference(_)));
            if let Expr::Reference(origin) = origin {
                let name = origin.as_ref().name.as_ref();
                assert!(matches!(name, Identifier { name, .. } if name == "x"));
            };
            let index = inner.as_ref().index.as_ref();
            assert!(matches!(index, Expr::Reference(_)));
            if let Expr::Reference(index) = index {
                let name = index.as_ref().name.as_ref();
                assert!(matches!(name, Identifier { name, .. } if name == "y"));
            };
        };
    }

    #[test]
    fn test_parse_call_expr() {
        let prod = assert_parse("x()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Call(_)));
        if let Expr::Call(inner) = *prod {
            let origin = inner.as_ref().callee.as_ref();
            let count = inner.as_ref().arguments.len();
            assert_eq!(count, 0);
            assert!(matches!(origin, Expr::Reference(_)));
            if let Expr::Reference(origin) = origin {
                let name = origin.as_ref().name.as_ref();
                assert!(matches!(name, Identifier { name, .. } if name == "x"));
            };
        };

        let prod = assert_parse("x(z)", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Call(_)));
        if let Expr::Call(inner) = *prod {
            let count = inner.as_ref().arguments.len();
            assert_eq!(count, 1);
        }

        let prod = assert_parse("x(z, foo(bar, baz()))", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Call(_)));
        if let Expr::Call(inner) = *prod {
            let count = inner.as_ref().arguments.len();
            assert_eq!(count, 2);
        }
    }

    #[test]
    fn test_parse_construct_expr() {
        let prod = assert_parse("x {}", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Construct(_)));
        if let Expr::Construct(inner) = *prod {
            let count = inner.as_ref().arguments.len();
            assert_eq!(count, 0);
        };

        let prod = assert_parse("x { y: z, }", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Construct(_)));
        if let Expr::Construct(inner) = *prod {
            let count = inner.as_ref().arguments.len();
            assert_eq!(count, 1);
        }

        let prod = assert_parse("x { y: notrailingcomma }", |p| p.parse_expr());
        assert_ok!(prod);
    }

    #[test]
    fn test_parse_unary_expr() {
        let prod = assert_parse("-x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::UnaryOp(_)));
        if let Expr::UnaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &UnaryOp::Neg);
        };

        let prod = assert_parse("*x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::UnaryOp(_)));
        if let Expr::UnaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &UnaryOp::Deref);
        };

        let prod = assert_parse("&x", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::UnaryOp(_)));
        if let Expr::UnaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &UnaryOp::AddressOf);
        };
    }

    #[test]
    fn test_parse_multiplicative_expr() {
        let prod = assert_parse("x + y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Add);
        };

        let prod = assert_parse("x * y / z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Mul);
        };
    }

    #[test]
    fn test_parse_additive_expr() {
        let prod = assert_parse("x - y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Sub);
        };

        let prod = assert_parse("x + y * z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            let rhs = inner.as_ref().rhs.as_ref();
            assert_eq!(op, &BinaryOp::Add);

            assert!(matches!(rhs, Expr::BinaryOp(_)));
            if let Expr::BinaryOp(inner) = rhs {
                let op = &inner.as_ref().op;
                assert_eq!(op, &BinaryOp::Mul);
            };
        };
    }

    #[test]
    fn test_parse_comparison_expr() {
        let prod = assert_parse("x < y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Lt);
        };

        let prod = assert_parse("x < y < z", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::BinaryOp(_)));
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Lt);

            let rhs = inner.as_ref().rhs.as_ref();
            assert!(matches!(rhs, Expr::BinaryOp(_)));
            if let Expr::BinaryOp(inner) = rhs {
                let op = &inner.as_ref().op;
                assert_eq!(op, &BinaryOp::Lt);
            };
        };
    }

    #[test]
    fn test_parse_logical_and_expr() {
        let prod = assert_parse("a + 3 && y", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::And);
        };
    }

    #[test]
    fn test_parse_logical_or_expr() {
        let prod = assert_parse("a || y()", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        if let Expr::BinaryOp(inner) = *prod {
            let op = &inner.as_ref().op;
            assert_eq!(op, &BinaryOp::Or);
        };
    }

    #[test]
    fn test_assign_expr() {
        let prod = assert_parse("a = 3", |p| p.parse_expr());
        let prod = assert_ok!(prod);
        assert!(matches!(*prod, Expr::Assign(_)));
    }

    #[test]
    fn test_parse_invalid_literal() {
        let mut parser = Parser::new(Lexer::new("let k = 1234773457276345671237572345;"));
        let prod = assert_err!(parser.parse_let_stmt());
        assert!(
            matches!(prod, ParseError::InvalidIntegerLiteral(InvalidIntegerLiteralError {
            span, ..
        }) if span.low == 8 && span.high == 36)
        );
    }
}
