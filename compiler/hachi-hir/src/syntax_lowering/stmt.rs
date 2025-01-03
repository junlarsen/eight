use crate::error::{BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult};
use crate::expr::{HirBooleanLiteralExpr, HirExpr};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::syntax_lowering::SyntaxLoweringPass;
use crate::ty::HirTy;
use hachi_span::Span;
use hachi_syntax::{BreakStmt, ContinueStmt, ExprStmt, ForStmt, IfStmt, LetStmt, ReturnStmt, Stmt};

impl<'ast> SyntaxLoweringPass<'ast> {
    pub fn visit_stmt(&mut self, node: &'ast Stmt) -> HirResult<Box<HirStmt>> {
        match node {
            Stmt::Let(s) => self.visit_let_stmt(s),
            Stmt::Return(s) => self.visit_return_stmt(s),
            Stmt::For(s) => self.visit_for_stmt(s),
            Stmt::Break(s) => self.visit_break_stmt(s),
            Stmt::Continue(s) => self.visit_continue_stmt(s),
            Stmt::If(s) => self.visit_if_stmt(s),
            Stmt::Expr(s) => self.visit_expr_stmt(s),
        }
    }

    pub fn visit_let_stmt(&mut self, node: &'ast LetStmt) -> HirResult<Box<HirStmt>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let r#type = match &node.r#type {
            Some(t) => self.visit_type(t)?,
            None => Box::new(HirTy::Uninitialized),
        };
        let value = self.visit_expr(node.value.as_ref())?;
        let hir = HirStmt::Let(HirLetStmt {
            span: node.span().clone(),
            name,
            r#type,
            value,
        });
        Ok(Box::new(hir))
    }

    pub fn visit_return_stmt(&mut self, node: &'ast ReturnStmt) -> HirResult<Box<HirStmt>> {
        let value = node
            .value
            .as_ref()
            .map(|v| self.visit_expr(v))
            .transpose()?;
        let hir = HirStmt::Return(HirReturnStmt {
            span: node.span().clone(),
            value,
        });
        Ok(Box::new(hir))
    }

    /// Translate a for statement into a loop and block statement.
    ///
    /// The following is the synthesis for a for loop, rewritten into using anonymous blocks:
    ///
    /// ```text
    /// for (let x = 1; x < 10; x = x + 1) { foo(); }
    ///
    /// {
    ///   let x = 1;
    ///   loop (x < 10) {
    ///     { foo(); }
    ///     { x = x + 1; }
    ///   }
    /// }
    /// ```
    ///
    /// The semantics of the lowering is as follows:
    ///
    /// - If the initializer is missing, then the induced `let` statement is replaced with a {}
    /// - If the condition is missing, then a literal true is used as the condition.
    /// - If the increment is missing, then the increment block is replaced with a {}
    pub fn visit_for_stmt(&mut self, node: &'ast ForStmt) -> HirResult<Box<HirStmt>> {
        self.loop_depth.push_back(node);
        // Build the let statement for the initializer
        let initializer = node
            .initializer
            .as_ref()
            .map(|i| -> HirResult<HirLetStmt> {
                Ok(HirLetStmt {
                    span: i.span().clone(),
                    name: self.visit_identifier(i.name.as_ref())?,
                    r#type: Box::new(HirTy::Uninitialized),
                    value: self.visit_expr(i.initializer.as_ref())?,
                })
            })
            .transpose()?;
        // Take the condition, or insert a `true` literal node
        let condition = node
            .condition
            .as_ref()
            .map(|c| self.visit_expr(c))
            .transpose()?
            .unwrap_or_else(|| {
                Box::new(HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
                    span: Span::empty(),
                    value: true,
                    ty: Box::new(HirTy::Uninitialized),
                }))
            });
        let increment = node
            .increment
            .as_ref()
            .map(|i| self.visit_expr(i))
            .transpose()?;
        let body = node
            .body
            .iter()
            .map(|s| self.visit_stmt(s))
            .collect::<HirResult<Vec<_>>>()?;
        // Build the new block statement with the loop
        let hir = HirStmt::Block(HirBlockStmt {
            span: node.span().clone(),
            body: vec![
                Box::new(initializer.map(HirStmt::Let).unwrap_or_else(|| {
                    HirStmt::Block(HirBlockStmt {
                        span: Span::empty(),
                        body: vec![],
                    })
                })),
                Box::new(HirStmt::Loop(HirLoopStmt {
                    span: node.span().clone(),
                    condition,
                    body: {
                        let mut stmts = body;
                        if let Some(i) = increment {
                            stmts.push(Box::new(HirStmt::Expr(HirExprStmt {
                                span: i.span().clone(),
                                expr: i,
                            })));
                        }
                        stmts
                    },
                })),
            ],
        });
        self.loop_depth.pop_back();
        Ok(Box::new(hir))
    }

    /// Translate an if statement into a conditional expression.
    ///
    /// The synthesis of the if statement simply replaces a missing unhappy path with an empty
    /// block.
    pub fn visit_if_stmt(&mut self, node: &'ast IfStmt) -> HirResult<Box<HirStmt>> {
        let condition = self.visit_expr(node.condition.as_ref())?;
        let happy_path = node
            .happy_path
            .iter()
            .map(|s| self.visit_stmt(s))
            .collect::<HirResult<Vec<_>>>()?;
        let unhappy_path = match &node.unhappy_path {
            Some(unhappy_path) => unhappy_path
                .iter()
                .map(|s| self.visit_stmt(s))
                .collect::<HirResult<Vec<_>>>()?,
            None => vec![],
        };
        let hir = HirStmt::If(HirIfStmt {
            span: node.span().clone(),
            condition,
            happy_path,
            unhappy_path,
        });
        Ok(Box::new(hir))
    }

    pub fn visit_break_stmt(&mut self, node: &'ast BreakStmt) -> HirResult<Box<HirStmt>> {
        self.loop_depth
            .back()
            .ok_or(HirError::BreakOutsideLoop(BreakOutsideLoopError {
                span: node.span().clone(),
            }))?;
        let hir = HirStmt::Break(HirBreakStmt {
            span: node.span().clone(),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_expr_stmt(&mut self, node: &'ast ExprStmt) -> HirResult<Box<HirStmt>> {
        let expr = self.visit_expr(node.expr.as_ref())?;
        let hir = HirStmt::Expr(HirExprStmt {
            span: node.span().clone(),
            expr,
        });
        Ok(Box::new(hir))
    }

    pub fn visit_continue_stmt(&mut self, node: &'ast ContinueStmt) -> HirResult<Box<HirStmt>> {
        self.loop_depth
            .back()
            .ok_or(HirError::ContinueOutsideLoop(ContinueOutsideLoopError {
                span: node.span().clone(),
            }))?;
        let hir = HirStmt::Continue(HirContinueStmt {
            span: node.span().clone(),
        });
        Ok(Box::new(hir))
    }
}
