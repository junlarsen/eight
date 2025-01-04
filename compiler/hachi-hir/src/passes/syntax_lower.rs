use crate::context::LocalContext;
use crate::error::{BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use crate::fun::{
    HirFun, HirFunction, HirFunctionParameter, HirFunctionTypeParameter, HirIntrinsicFunction,
};
use crate::rec::{HirRecord, HirRecordField};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::HirTy;
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
/// fresh type variable.
pub struct SyntaxLoweringPass<'ast> {
    loop_depth: VecDeque<&'ast ForStmt>,
    generic_substitutions: LocalContext<HirTy>,
    function_depth: VecDeque<&'ast FunctionItem>,
}

impl SyntaxLoweringPass<'_> {
    pub fn new() -> Self {
        Self {
            loop_depth: VecDeque::new(),
            generic_substitutions: LocalContext::new(),
            function_depth: VecDeque::new(),
        }
    }
}

impl<'ast> SyntaxLoweringPass<'ast> {
    pub fn visit_expr(&mut self, node: &'ast Expr) -> HirResult<Box<HirExpr>> {
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

    pub fn visit_assign_expr(&mut self, node: &'ast AssignExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Assign(HirAssignExpr {
            span: node.span().clone(),
            lhs: self.visit_expr(node.lhs.as_ref())?,
            rhs: self.visit_expr(node.rhs.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_call_expr(&mut self, node: &'ast CallExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Call(HirCallExpr {
            span: node.span().clone(),
            callee: self.visit_expr(node.callee.as_ref())?,
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_expr(a))
                .collect::<HirResult<Vec<_>>>()?,
            type_arguments: node
                .type_arguments
                .iter()
                .map(|t| self.visit_type(t))
                .collect::<HirResult<Vec<_>>>()?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_construct_expr(&mut self, node: &'ast ConstructExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Construct(HirConstructExpr {
            span: node.span().clone(),
            callee: self.visit_type(node.callee.as_ref())?,
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_constructor_expr_argument(a))
                .collect::<HirResult<Vec<_>>>()?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_constructor_expr_argument(
        &mut self,
        node: &'ast ConstructorExprArgument,
    ) -> HirResult<Box<HirConstructExprArgument>> {
        let hir = HirConstructExprArgument {
            span: node.span().clone(),
            field: self.visit_identifier(node.field.as_ref())?,
            expr: self.visit_expr(node.expr.as_ref())?,
        };
        Ok(Box::new(hir))
    }

    pub fn visit_group_expr(&mut self, node: &'ast GroupExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Group(HirGroupExpr {
            span: node.span().clone(),
            inner: self.visit_expr(node.inner.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        node: &'ast IntegerLiteralExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::IntegerLiteral(HirIntegerLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        node: &'ast BooleanLiteralExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    /// Visit a unary operator expression.
    ///
    /// We translate the AddressOf and Deref operators into separate expressions, as they produce
    /// different types
    pub fn visit_unary_op_expr(&mut self, node: &'ast UnaryOpExpr) -> HirResult<Box<HirExpr>> {
        let hir = match &node.op {
            UnaryOp::Not | UnaryOp::Neg => HirExpr::UnaryOp(HirUnaryOpExpr {
                span: node.span().clone(),
                operand: self.visit_expr(node.operand.as_ref())?,
                op: self.visit_unary_op(&node.op)?,
                ty: Box::new(HirTy::Uninitialized),
            }),
            UnaryOp::Deref => HirExpr::Deref(HirDerefExpr {
                span: node.span().clone(),
                inner: self.visit_expr(node.operand.as_ref())?,
                ty: Box::new(HirTy::Uninitialized),
            }),
            UnaryOp::AddressOf => HirExpr::AddressOf(HirAddressOfExpr {
                span: node.span().clone(),
                inner: self.visit_expr(node.operand.as_ref())?,
                ty: Box::new(HirTy::Uninitialized),
            }),
        };
        Ok(Box::new(hir))
    }

    pub fn visit_binary_op_expr(&mut self, node: &'ast BinaryOpExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::BinaryOp(HirBinaryOpExpr {
            span: node.span().clone(),
            lhs: self.visit_expr(node.lhs.as_ref())?,
            rhs: self.visit_expr(node.rhs.as_ref())?,
            op: self.visit_binary_op(&node.op)?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_dot_index_expr(&mut self, node: &'ast DotIndexExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::ConstantIndex(HirConstantIndexExpr {
            span: node.span().clone(),
            origin: self.visit_expr(node.origin.as_ref())?,
            index: self.visit_identifier(node.index.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_bracket_index_expr(
        &mut self,
        node: &'ast BracketIndexExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::OffsetIndex(HirOffsetIndexExpr {
            span: node.span().clone(),
            origin: self.visit_expr(node.origin.as_ref())?,
            index: self.visit_expr(node.index.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_reference_expr(&mut self, node: &'ast ReferenceExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Reference(HirReferenceExpr {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
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

    pub fn visit_translation_unit(&mut self, node: &'ast TranslationUnit) -> HirResult<HirModule> {
        let mut module = HirModule::new();
        for item in &node.items {
            self.visit_item(&mut module, item)?;
        }
        Ok(module)
    }

    pub fn visit_item(&mut self, module: &mut HirModule, node: &'ast Item) -> HirResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(module, f),
            Item::IntrinsicFunction(f) => self.visit_intrinsic_function_item(module, f),
            Item::Type(t) => self.visit_type_item(module, t),
        }
    }

    pub fn visit_function_item(
        &mut self,
        module: &mut HirModule,
        node: &'ast FunctionItem,
    ) -> HirResult<()> {
        self.function_depth.push_back(node);
        // When we enter a function, we substitute all the type parameters with fresh type variables
        // so that the type checker knows these are generic types, and not constants. It is
        // currently safe to assume index for the type parameters, as we don't have higher order
        // functions or lambdas.
        self.generic_substitutions.enter_scope();
        let mut type_parameters = Vec::new();
        for (variable, type_parameter) in node.type_parameters.iter().enumerate() {
            self.generic_substitutions.add(
                &type_parameter.name.name,
                HirTy::new_var(variable, type_parameter.span().clone()),
            );
            // We also build the HIR representation, preserving the original name that was written
            // in code.
            let hir = self.visit_function_type_parameter(type_parameter, variable)?;
            type_parameters.push(hir);
        }
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => Box::new(HirTy::new_unit(&Span::empty())),
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

        let fun = HirFun::Function(HirFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
            body,
        });
        self.generic_substitutions.leave_scope();
        self.function_depth.pop_back();
        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        module: &mut HirModule,
        node: &'ast IntrinsicFunctionItem,
    ) -> HirResult<()> {
        self.generic_substitutions.enter_scope();
        let mut type_parameters = Vec::new();
        for (variable, type_parameter) in node.type_parameters.iter().enumerate() {
            self.generic_substitutions.add(
                &type_parameter.name.name,
                HirTy::new_var(variable, type_parameter.span().clone()),
            );
            // We also build the HIR representation, preserving the original name that was written
            // in code.
            let hir = self.visit_function_type_parameter(type_parameter, variable)?;
            type_parameters.push(hir);
        }

        let return_type = self.visit_type(node.return_type.as_ref())?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;

        let fun = HirFun::Intrinsic(HirIntrinsicFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
        });
        self.generic_substitutions.leave_scope();

        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &'ast FunctionParameterItem,
    ) -> HirResult<Box<HirFunctionParameter>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let ty = self.visit_type(node.r#type.as_ref())?;
        let hir = HirFunctionParameter {
            span: node.span().clone(),
            name,
            ty,
        };
        Ok(Box::new(hir))
    }

    pub fn visit_function_type_parameter(
        &mut self,
        node: &'ast FunctionTypeParameterItem,
        substitution_name: usize,
    ) -> HirResult<Box<HirFunctionTypeParameter>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let hir = HirFunctionTypeParameter {
            span: node.span().clone(),
            name: substitution_name,
            syntax_name: name,
        };
        Ok(Box::new(hir))
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
        module: &mut HirModule,
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
                    ty,
                    span: member.span().clone(),
                };
                Ok((member.name.name.to_owned(), Box::new(field)))
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
    pub fn visit_type(&mut self, node: &Type) -> HirResult<Box<HirTy>> {
        let ty = match node {
            Type::Unit(_) => HirTy::new_unit(node.span()),
            Type::Integer32(_) => HirTy::new_i32(node.span()),
            Type::Boolean(_) => HirTy::new_bool(node.span()),
            // If the type is referring to a generic type that we have substituted before, we
            // use replace it with the substitution
            Type::Named(t) => match self.generic_substitutions.find(&t.name.name) {
                Some(ty) => ty.clone(),
                None => HirTy::new_nominal(self.visit_identifier(t.name.as_ref())?, node.span()),
            },
            Type::Pointer(t) => HirTy::new_ptr(self.visit_type(t.inner.as_ref())?, node.span()),
        };
        Ok(Box::new(ty))
    }
}

impl Default for SyntaxLoweringPass<'_> {
    fn default() -> Self {
        Self::new()
    }
}
