use crate::error::{BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use crate::fun::{
    HirFunction, HirFunctionParameter, HirFunctionTypeParameter, HirIntrinsicFunction,
};
use crate::rec::{HirRecord, HirRecordField};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::{HirArena, HirTy};
use crate::{HirModule, HirName};
use hachi_diagnostics::ice;
use hachi_span::Span;
use hachi_syntax::{
    AssignExpr, BinaryOp, BinaryOpExpr, BooleanLiteralExpr, BracketIndexExpr, BreakStmt, CallExpr,
    ConstructExpr, ConstructorExprArgument, ContinueStmt, DotIndexExpr, Expr, ExprStmt, ForStmt,
    FunctionItem, FunctionParameterItem, FunctionTypeParameterItem, GroupExpr, Identifier, IfStmt,
    IntegerLiteralExpr, IntrinsicFunctionItem, Item, LetStmt, ReferenceExpr, ReturnStmt, Stmt,
    TranslationUnit, Type, TypeItem, UnaryOp, UnaryOpExpr,
};
use std::collections::{BTreeMap, VecDeque};

/// Translation pass that lowers the `hachi-syntax` AST into the HIR representation.
///
/// This pass is responsible for lowering syntactic sugar into the HIR nodes. It also does some very
/// basic semantic analysis, such as checking `return` and `break`/`continue` statement contexts.
///
/// All types (note: generic types too) are preserved, meaning that a generic type like `T` will be
/// lowered into a TConst type, despite the fact that the type checker will replace this with a
/// fresh type variable. This is to allow the type checker to generate a fresh type variable for
/// each type parameter for the local context.
pub struct ASTSyntaxLoweringPass<'ast, 'ta> {
    arena: &'ta HirArena<'ta>,
    loop_depth: VecDeque<&'ast ForStmt>,
}

impl<'ast, 'ta> ASTSyntaxLoweringPass<'ast, 'ta> {
    pub fn new(arena: &'ta HirArena<'ta>) -> Self {
        Self {
            arena,
            loop_depth: VecDeque::new(),
        }
    }
}

impl<'ast, 'ta> ASTSyntaxLoweringPass<'ast, 'ta> {
    pub fn visit_expr(&mut self, node: &'ast Expr) -> HirResult<HirExpr<'ta>> {
        match node {
            Expr::Assign(e) => self.visit_assign_expr(e),
            Expr::Call(e) => self.visit_call_expr(e),
            Expr::Construct(e) => self.visit_construct_expr(e),
            Expr::Group(e) => self.visit_group_expr(e),
            Expr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            Expr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            Expr::UnaryOp(e) => self.visit_unary_op_expr(e),
            Expr::BinaryOp(e) => self.visit_binary_op_expr(e),
            Expr::DotIndex(e) => self.visit_dot_index_expr(e),
            Expr::BracketIndex(e) => self.visit_bracket_index_expr(e),
            Expr::Reference(e) => self.visit_reference_expr(e),
        }
    }

    pub fn visit_assign_expr(&mut self, node: &'ast AssignExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Assign(HirAssignExpr {
            span: node.span().clone(),
            lhs: Box::new(self.visit_expr(node.lhs.as_ref())?),
            rhs: Box::new(self.visit_expr(node.rhs.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_call_expr(&mut self, node: &'ast CallExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Call(HirCallExpr {
            span: node.span().clone(),
            callee: Box::new(self.visit_expr(node.callee.as_ref())?),
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_expr(a).map(Box::new))
                .collect::<HirResult<Vec<_>>>()?,
            type_arguments: node
                .type_arguments
                .iter()
                .map(|t| self.visit_type(t))
                .collect::<HirResult<Vec<_>>>()?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_construct_expr(&mut self, node: &'ast ConstructExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Construct(HirConstructExpr {
            span: node.span().clone(),
            callee: self.visit_type(node.callee.as_ref())?,
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_constructor_expr_argument(a))
                .collect::<HirResult<Vec<_>>>()?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_constructor_expr_argument(
        &mut self,
        node: &'ast ConstructorExprArgument,
    ) -> HirResult<HirConstructExprArgument<'ta>> {
        let hir = HirConstructExprArgument {
            span: node.span().clone(),
            field: self.visit_identifier(node.field.as_ref())?,
            expr: Box::new(self.visit_expr(node.expr.as_ref())?),
        };
        Ok(hir)
    }

    pub fn visit_group_expr(&mut self, node: &'ast GroupExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Group(HirGroupExpr {
            span: node.span().clone(),
            inner: Box::new(self.visit_expr(node.inner.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        node: &'ast IntegerLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::IntegerLiteral(HirIntegerLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        node: &'ast BooleanLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    /// Visit a unary operator expression.
    ///
    /// We translate the AddressOf and Deref operators into separate expressions, as they produce
    /// different types
    pub fn visit_unary_op_expr(&mut self, node: &'ast UnaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = match &node.op {
            UnaryOp::Not | UnaryOp::Neg => HirExpr::UnaryOp(HirUnaryOpExpr {
                span: node.span().clone(),
                operand: Box::new(self.visit_expr(node.operand.as_ref())?),
                op: self.visit_unary_op(&node.op)?,
                ty: self.arena.get_uninitialized_ty(),
            }),
            UnaryOp::Deref => HirExpr::Deref(HirDerefExpr {
                span: node.span().clone(),
                inner: Box::new(self.visit_expr(node.operand.as_ref())?),
                ty: self.arena.get_uninitialized_ty(),
            }),
            UnaryOp::AddressOf => HirExpr::AddressOf(HirAddressOfExpr {
                span: node.span().clone(),
                inner: Box::new(self.visit_expr(node.operand.as_ref())?),
                ty: self.arena.get_uninitialized_ty(),
            }),
        };
        Ok(hir)
    }

    pub fn visit_binary_op_expr(&mut self, node: &'ast BinaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BinaryOp(HirBinaryOpExpr {
            span: node.span().clone(),
            lhs: Box::new(self.visit_expr(node.lhs.as_ref())?),
            rhs: Box::new(self.visit_expr(node.rhs.as_ref())?),
            op: self.visit_binary_op(&node.op)?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_dot_index_expr(&mut self, node: &'ast DotIndexExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::ConstantIndex(HirConstantIndexExpr {
            span: node.span().clone(),
            origin: Box::new(self.visit_expr(node.origin.as_ref())?),
            index: self.visit_identifier(node.index.as_ref())?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_bracket_index_expr(
        &mut self,
        node: &'ast BracketIndexExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::OffsetIndex(HirOffsetIndexExpr {
            span: node.span().clone(),
            origin: Box::new(self.visit_expr(node.origin.as_ref())?),
            index: Box::new(self.visit_expr(node.index.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_reference_expr(&mut self, node: &'ast ReferenceExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Reference(HirReferenceExpr {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_unary_op(&mut self, node: &'ast UnaryOp) -> HirResult<HirUnaryOp> {
        match node {
            UnaryOp::Not => Ok(HirUnaryOp::Not),
            UnaryOp::Neg => Ok(HirUnaryOp::Neg),
            _ => ice!("visit_unary_op called addressof or deref operator"),
        }
    }

    pub fn visit_binary_op(&mut self, node: &'ast BinaryOp) -> HirResult<HirBinaryOp> {
        match node {
            BinaryOp::Add => Ok(HirBinaryOp::Add),
            BinaryOp::Sub => Ok(HirBinaryOp::Sub),
            BinaryOp::Mul => Ok(HirBinaryOp::Mul),
            BinaryOp::Div => Ok(HirBinaryOp::Div),
            BinaryOp::Rem => Ok(HirBinaryOp::Rem),
            BinaryOp::Eq => Ok(HirBinaryOp::Eq),
            BinaryOp::Neq => Ok(HirBinaryOp::Neq),
            BinaryOp::Lt => Ok(HirBinaryOp::Lt),
            BinaryOp::Gt => Ok(HirBinaryOp::Gt),
            BinaryOp::Le => Ok(HirBinaryOp::Le),
            BinaryOp::Ge => Ok(HirBinaryOp::Ge),
            BinaryOp::Lte => Ok(HirBinaryOp::Lte),
            BinaryOp::Gte => Ok(HirBinaryOp::Gte),
            BinaryOp::And => Ok(HirBinaryOp::And),
            BinaryOp::Or => Ok(HirBinaryOp::Or),
        }
    }

    pub fn visit_translation_unit(
        &mut self,
        node: &'ast TranslationUnit,
    ) -> HirResult<HirModule<'ta>> {
        let mut module = HirModule::new(self.arena);
        for item in &node.items {
            self.visit_item(&mut module, item)?;
        }
        Ok(module)
    }

    pub fn visit_item(&mut self, module: &mut HirModule<'ta>, node: &'ast Item) -> HirResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(module, f),
            Item::IntrinsicFunction(f) => self.visit_intrinsic_function_item(module, f),
            Item::Type(t) => self.visit_type_item(module, t),
        }
    }

    pub fn visit_function_item(
        &mut self,
        module: &mut HirModule<'ta>,
        node: &'ast FunctionItem,
    ) -> HirResult<()> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_function_type_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = node.return_type.as_ref().map(|t| t.span().clone());
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.arena.get_unit_ty(),
        };
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let body = node
            .body
            .iter()
            .map(|stmt| self.visit_stmt(stmt))
            .collect::<HirResult<Vec<_>>>()?;
        let fun = HirFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
            return_type_annotation,
            body,
        };
        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        module: &mut HirModule<'ta>,
        node: &'ast IntrinsicFunctionItem,
    ) -> HirResult<()> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_function_type_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = node.return_type.span().clone();
        let return_type = self.visit_type(node.return_type.as_ref())?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;

        let fun = HirIntrinsicFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
            return_type_annotation,
        };
        module
            .intrinsic_functions
            .insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &'ast FunctionParameterItem,
    ) -> HirResult<HirFunctionParameter<'ta>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let ty = self.visit_type(node.r#type.as_ref())?;
        let hir = HirFunctionParameter {
            span: node.span().clone(),
            name,
            r#type: ty,
            type_annotation: node.r#type.span().clone(),
        };
        Ok(hir)
    }

    pub fn visit_function_type_parameter(
        &mut self,
        node: &'ast FunctionTypeParameterItem,
    ) -> HirResult<HirFunctionTypeParameter> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let hir = HirFunctionTypeParameter {
            span: node.span().clone(),
            syntax_name: name,
        };
        Ok(hir)
    }

    /// Declare a type item.
    ///
    /// We insert the type's structure into the module, and then derive the HIR type for each of the
    /// type members.
    ///
    /// This function does not check validity of the type members, as this is only a forward
    /// declaration. We have to do it like this in order to be able to support recursive types.
    ///
    /// While we do not support infinitely recursive types, we still need to support the following:
    ///
    /// ```text
    /// type Node = { value: i32, left: *Node, right: *Node, }
    /// ```
    pub fn visit_type_item(
        &mut self,
        module: &mut HirModule<'ta>,
        node: &'ast TypeItem,
    ) -> HirResult<()> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let fields = node
            .members
            .iter()
            .map(|member| {
                let ty = self.visit_type(member.r#type.as_ref())?;
                let field = HirRecordField {
                    name: self.visit_identifier(member.name.as_ref())?,
                    r#type: ty,
                    type_annotation: member.r#type.span().clone(),
                    span: member.span().clone(),
                };
                Ok((member.name.name.to_owned(), field))
            })
            .collect::<HirResult<BTreeMap<_, _>>>()?;
        let rec = HirRecord {
            name,
            fields,
            span: node.span().clone(),
        };
        module.records.insert(node.name.name.to_owned(), rec);
        Ok(())
    }

    pub fn visit_stmt(&mut self, node: &'ast Stmt) -> HirResult<HirStmt<'ta>> {
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

    pub fn visit_let_stmt(&mut self, node: &'ast LetStmt) -> HirResult<HirStmt<'ta>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let r#type = match &node.r#type {
            Some(t) => self.visit_type(t)?,
            None => self.arena.get_uninitialized_ty(),
        };
        let value = self.visit_expr(node.value.as_ref())?;
        let hir = HirStmt::Let(HirLetStmt {
            span: node.span().clone(),
            name,
            r#type,
            type_annotation: node.r#type.as_ref().map(|t| t.span().clone()),
            value: Box::new(value),
        });
        Ok(hir)
    }

    pub fn visit_return_stmt(&mut self, node: &'ast ReturnStmt) -> HirResult<HirStmt<'ta>> {
        let value = node
            .value
            .as_ref()
            .map(|v| self.visit_expr(v))
            .transpose()?;
        let hir = HirStmt::Return(HirReturnStmt {
            span: node.span().clone(),
            value: value.map(Box::new),
        });
        Ok(hir)
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
    pub fn visit_for_stmt(&mut self, node: &'ast ForStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth.push_back(node);
        // Build the let statement for the initializer
        let initializer = node
            .initializer
            .as_ref()
            .map(|i| -> HirResult<HirLetStmt> {
                Ok(HirLetStmt {
                    span: i.span().clone(),
                    name: self.visit_identifier(i.name.as_ref())?,
                    r#type: self.arena.get_uninitialized_ty(),
                    type_annotation: None,
                    value: Box::new(self.visit_expr(i.initializer.as_ref())?),
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
                HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
                    span: Span::empty(),
                    value: true,
                    ty: self.arena.get_uninitialized_ty(),
                })
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
                    condition: Box::new(condition),
                    body: {
                        let mut stmts = body;
                        if let Some(i) = increment {
                            stmts.push(HirStmt::Expr(HirExprStmt {
                                span: i.span().clone(),
                                expr: Box::new(i),
                            }));
                        }
                        stmts
                    },
                })),
            ],
        });
        self.loop_depth.pop_back();
        Ok(hir)
    }

    /// Translate an if statement into a conditional expression.
    ///
    /// The synthesis of the if statement simply replaces a missing unhappy path with an empty
    /// block.
    pub fn visit_if_stmt(&mut self, node: &'ast IfStmt) -> HirResult<HirStmt<'ta>> {
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
            condition: Box::new(condition),
            happy_path,
            unhappy_path,
        });
        Ok(hir)
    }

    pub fn visit_break_stmt(&mut self, node: &'ast BreakStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .back()
            .ok_or(HirError::BreakOutsideLoop(BreakOutsideLoopError {
                span: node.span().clone(),
            }))?;
        let hir = HirStmt::Break(HirBreakStmt {
            span: node.span().clone(),
        });
        Ok(hir)
    }

    pub fn visit_expr_stmt(&mut self, node: &'ast ExprStmt) -> HirResult<HirStmt<'ta>> {
        let expr = self.visit_expr(node.expr.as_ref())?;
        let hir = HirStmt::Expr(HirExprStmt {
            span: node.span().clone(),
            expr: Box::new(expr),
        });
        Ok(hir)
    }

    pub fn visit_continue_stmt(&mut self, node: &'ast ContinueStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .back()
            .ok_or(HirError::ContinueOutsideLoop(ContinueOutsideLoopError {
                span: node.span().clone(),
            }))?;
        let hir = HirStmt::Continue(HirContinueStmt {
            span: node.span().clone(),
        });
        Ok(hir)
    }

    /// Translate a syntax identifier into a HIR name.
    pub fn visit_identifier(&mut self, node: &Identifier) -> HirResult<HirName> {
        Ok(HirName {
            name: node.name.to_owned(),
            span: node.span().clone(),
        })
    }

    /// Translate a syntax type into a HIR type.
    ///
    /// This function preserves generic types, and will simply replace T in the following code with
    /// a Const type. It is the job of the type-checker pass to replace this TConst type with a
    /// type variable using its type environment.
    ///
    /// ```text
    /// fn foo<T>(x: T) -> T {}
    /// ```
    #[allow(clippy::only_used_in_recursion)]
    pub fn visit_type(&mut self, node: &Type) -> HirResult<&'ta HirTy<'ta>> {
        let ty = match node {
            Type::Unit(_) => self.arena.get_unit_ty(),
            Type::Integer32(_) => self.arena.get_integer32_ty(),
            Type::Boolean(_) => self.arena.get_boolean_ty(),
            Type::Named(t) => self
                .arena
                .get_nominal_ty(&self.visit_identifier(t.name.as_ref())?),
            Type::Pointer(t) => self
                .arena
                .get_pointer_ty(self.visit_type(t.inner.as_ref())?),
        };
        Ok(ty)
    }
}
