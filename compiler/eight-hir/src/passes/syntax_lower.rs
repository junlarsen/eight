use crate::arena::HirArena;
use crate::error::{BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use crate::item::{
    HirFunction, HirFunctionParameter, HirInstance, HirIntrinsicFunction, HirIntrinsicScalar,
    HirRecord, HirRecordField, HirTrait, HirTraitFunctionItem, HirTypeParameter,
};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::HirTy;
use crate::{HirModule, HirName};
use eight_diagnostics::ice;
use eight_span::Span;
use eight_syntax::{
    AstAssignExpr, AstBinaryOp, AstBinaryOpExpr, AstBooleanLiteralExpr, AstBracketIndexExpr,
    AstBreakStmt, AstCallExpr, AstConstructExpr, AstConstructorExprArgument, AstContinueStmt,
    AstDotIndexExpr, AstExpr, AstExprStmt, AstForStmt, AstFunctionItem, AstFunctionParameterItem,
    AstGroupExpr, AstIdentifier, AstIfStmt, AstInstanceItem, AstIntegerLiteralExpr,
    AstIntrinsicFunctionItem, AstIntrinsicScalarItem, AstItem, AstLetStmt, AstReferenceExpr,
    AstReturnStmt, AstStmt, AstTraitFunctionItem, AstTraitItem, AstTranslationUnit, AstType,
    AstTypeItem, AstTypeParameterItem, AstUnaryOp, AstUnaryOpExpr,
};
use std::collections::{BTreeMap, VecDeque};

/// Translation pass that lowers the `eight-syntax` AST into the HIR representation.
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
    loop_depth: VecDeque<&'ast AstForStmt>,
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
    pub fn visit_expr(&mut self, node: &'ast AstExpr) -> HirResult<HirExpr<'ta>> {
        match node {
            AstExpr::Assign(e) => self.visit_assign_expr(e),
            AstExpr::Call(e) => self.visit_call_expr(e),
            AstExpr::Construct(e) => self.visit_construct_expr(e),
            AstExpr::Group(e) => self.visit_group_expr(e),
            AstExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            AstExpr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            AstExpr::UnaryOp(e) => self.visit_unary_op_expr(e),
            AstExpr::BinaryOp(e) => self.visit_binary_op_expr(e),
            AstExpr::DotIndex(e) => self.visit_dot_index_expr(e),
            AstExpr::BracketIndex(e) => self.visit_bracket_index_expr(e),
            AstExpr::Reference(e) => self.visit_reference_expr(e),
        }
    }

    pub fn visit_assign_expr(&mut self, node: &'ast AstAssignExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Assign(HirAssignExpr {
            span: node.span,
            lhs: Box::new(self.visit_expr(node.lhs.as_ref())?),
            rhs: Box::new(self.visit_expr(node.rhs.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_call_expr(&mut self, node: &'ast AstCallExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Call(HirCallExpr {
            span: node.span,
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

    pub fn visit_construct_expr(
        &mut self,
        node: &'ast AstConstructExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Construct(HirConstructExpr {
            span: node.span,
            callee: self.visit_type(&node.callee)?,
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
        node: &'ast AstConstructorExprArgument,
    ) -> HirResult<HirConstructExprArgument<'ta>> {
        let hir = HirConstructExprArgument {
            span: node.span,
            field: self.visit_identifier(&node.field)?,
            expr: Box::new(self.visit_expr(&node.expr)?),
        };
        Ok(hir)
    }

    pub fn visit_group_expr(&mut self, node: &'ast AstGroupExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Group(HirGroupExpr {
            span: node.span,
            inner: Box::new(self.visit_expr(node.inner.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        node: &'ast AstIntegerLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::IntegerLiteral(HirIntegerLiteralExpr {
            span: node.span,
            value: node.value,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        node: &'ast AstBooleanLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
            span: node.span,
            value: node.value,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    /// Visit a unary operator expression.
    ///
    /// We translate the AddressOf and Deref operators into separate expressions, as they produce
    /// different types
    pub fn visit_unary_op_expr(&mut self, node: &'ast AstUnaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = match &node.op {
            AstUnaryOp::Not | AstUnaryOp::Neg => HirExpr::UnaryOp(HirUnaryOpExpr {
                span: node.span,
                operand: Box::new(self.visit_expr(node.operand.as_ref())?),
                op: self.visit_unary_op(&node.op)?,
                ty: self.arena.get_uninitialized_ty(),
            }),
            AstUnaryOp::Deref => HirExpr::Deref(HirDerefExpr {
                span: node.span,
                inner: Box::new(self.visit_expr(node.operand.as_ref())?),
                ty: self.arena.get_uninitialized_ty(),
            }),
            AstUnaryOp::AddressOf => HirExpr::AddressOf(HirAddressOfExpr {
                span: node.span,
                inner: Box::new(self.visit_expr(node.operand.as_ref())?),
                ty: self.arena.get_uninitialized_ty(),
            }),
        };
        Ok(hir)
    }

    pub fn visit_binary_op_expr(&mut self, node: &'ast AstBinaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BinaryOp(HirBinaryOpExpr {
            span: node.span,
            lhs: Box::new(self.visit_expr(node.lhs.as_ref())?),
            rhs: Box::new(self.visit_expr(node.rhs.as_ref())?),
            op: self.visit_binary_op(&node.op)?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_dot_index_expr(&mut self, node: &'ast AstDotIndexExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::ConstantIndex(HirConstantIndexExpr {
            span: node.span,
            origin: Box::new(self.visit_expr(node.origin.as_ref())?),
            index: self.visit_identifier(&node.index)?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_bracket_index_expr(
        &mut self,
        node: &'ast AstBracketIndexExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::OffsetIndex(HirOffsetIndexExpr {
            span: node.span,
            origin: Box::new(self.visit_expr(node.origin.as_ref())?),
            index: Box::new(self.visit_expr(node.index.as_ref())?),
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_reference_expr(
        &mut self,
        node: &'ast AstReferenceExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Reference(HirReferenceExpr {
            span: node.span,
            name: self.visit_identifier(&node.name)?,
            ty: self.arena.get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_unary_op(&mut self, node: &'ast AstUnaryOp) -> HirResult<HirUnaryOp> {
        match node {
            AstUnaryOp::Not => Ok(HirUnaryOp::Not),
            AstUnaryOp::Neg => Ok(HirUnaryOp::Neg),
            _ => ice!("visit_unary_op called addressof or deref operator"),
        }
    }

    pub fn visit_binary_op(&mut self, node: &'ast AstBinaryOp) -> HirResult<HirBinaryOp> {
        match node {
            AstBinaryOp::Add => Ok(HirBinaryOp::Add),
            AstBinaryOp::Sub => Ok(HirBinaryOp::Sub),
            AstBinaryOp::Mul => Ok(HirBinaryOp::Mul),
            AstBinaryOp::Div => Ok(HirBinaryOp::Div),
            AstBinaryOp::Rem => Ok(HirBinaryOp::Rem),
            AstBinaryOp::Eq => Ok(HirBinaryOp::Eq),
            AstBinaryOp::Neq => Ok(HirBinaryOp::Neq),
            AstBinaryOp::Lt => Ok(HirBinaryOp::Lt),
            AstBinaryOp::Gt => Ok(HirBinaryOp::Gt),
            AstBinaryOp::Le => Ok(HirBinaryOp::Le),
            AstBinaryOp::Ge => Ok(HirBinaryOp::Ge),
            AstBinaryOp::Lte => Ok(HirBinaryOp::Lte),
            AstBinaryOp::Gte => Ok(HirBinaryOp::Gte),
            AstBinaryOp::And => Ok(HirBinaryOp::And),
            AstBinaryOp::Or => Ok(HirBinaryOp::Or),
        }
    }

    pub fn visit_translation_unit(
        &mut self,
        node: &'ast AstTranslationUnit,
    ) -> HirResult<HirModule<'ta>> {
        let mut module = HirModule::new();
        for item in &node.items {
            self.visit_item(&mut module, item)?;
        }
        Ok(module)
    }

    pub fn visit_item(
        &mut self,
        module: &mut HirModule<'ta>,
        node: &'ast AstItem,
    ) -> HirResult<()> {
        match node {
            AstItem::Function(f) => {
                module
                    .functions
                    .insert(f.name.name.to_owned(), self.visit_function_item(f)?);
                Ok(())
            }
            AstItem::IntrinsicFunction(f) => {
                module.intrinsic_functions.insert(
                    f.name.name.to_owned(),
                    self.visit_intrinsic_function_item(f)?,
                );
                Ok(())
            }
            AstItem::Type(t) => {
                module
                    .records
                    .insert(t.name.name.to_owned(), self.visit_type_item(t)?);
                Ok(())
            }
            AstItem::IntrinsicScalar(s) => {
                module
                    .intrinsic_scalars
                    .insert(s.name.name.to_owned(), self.visit_intrinsic_scalar_item(s)?);
                Ok(())
            }
            AstItem::Trait(t) => {
                module
                    .traits
                    .insert(t.name.name.to_owned(), self.visit_trait_item(t)?);
                Ok(())
            }
            AstItem::Instance(i) => {
                let instances = module
                    .instances
                    .entry(i.name.name.to_owned())
                    .or_default();
                instances.push(self.visit_instance_item(i)?);
                Ok(())
            }
        }
    }

    pub fn visit_function_item(
        &mut self,
        node: &'ast AstFunctionItem,
    ) -> HirResult<HirFunction<'ta>> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parmeter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = node.return_type.as_ref().map(|t| *t.span());
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
            span: node.span,
            name: self.visit_identifier(&node.name)?,
            type_parameters,
            parameters,
            return_type,
            return_type_annotation,
            body,
        };
        Ok(fun)
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        node: &'ast AstIntrinsicFunctionItem,
    ) -> HirResult<HirIntrinsicFunction<'ta>> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parmeter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = *node.return_type.span();
        let return_type = self.visit_type(&node.return_type)?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;

        let fun = HirIntrinsicFunction {
            span: node.span,
            name: self.visit_identifier(&node.name)?,
            type_parameters,
            parameters,
            return_type,
            return_type_annotation,
        };
        Ok(fun)
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &'ast AstFunctionParameterItem,
    ) -> HirResult<HirFunctionParameter<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let ty = self.visit_type(&node.ty)?;
        let hir = HirFunctionParameter {
            span: node.span,
            name,
            ty,
            type_annotation: *node.ty.span(),
        };
        Ok(hir)
    }

    pub fn visit_type_parmeter_item(
        &mut self,
        node: &'ast AstTypeParameterItem,
    ) -> HirResult<HirTypeParameter<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let hir = HirTypeParameter {
            span: node.span,
            syntax_name: name,
            substitution_name: None,
        };
        Ok(hir)
    }

    pub fn visit_intrinsic_scalar_item(
        &mut self,
        node: &'ast AstIntrinsicScalarItem,
    ) -> HirResult<HirIntrinsicScalar<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let scalar = HirIntrinsicScalar {
            name: name.name.to_owned(),
            ty: self.arena.get_integer32_ty(),
        };
        Ok(scalar)
    }

    pub fn visit_trait_item(&mut self, node: &'ast AstTraitItem) -> HirResult<HirTrait<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parmeter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let members = node
            .members
            .iter()
            .map(|m| self.visit_trait_function_item(m))
            .collect::<HirResult<Vec<_>>>()?;
        let r#trait = HirTrait {
            span: node.span,
            name,
            type_parameters,
            members,
        };
        Ok(r#trait)
    }

    pub fn visit_trait_function_item(
        &mut self,
        node: &'ast AstTraitFunctionItem,
    ) -> HirResult<HirTraitFunctionItem<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parmeter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.arena.get_unit_ty(),
        };
        let return_type_annotation = node.return_type.as_ref().map(|t| *t.span());
        let fun = HirTraitFunctionItem {
            span: node.span,
            name,
            type_parameters,
            parameters,
            return_type,
            return_type_annotation,
        };
        Ok(fun)
    }

    pub fn visit_instance_item(
        &mut self,
        node: &'ast AstInstanceItem,
    ) -> HirResult<HirInstance<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let instantiation_type_parameters = node
            .instantiation_type_parameters
            .iter()
            .map(|t| self.visit_type(t))
            .collect::<HirResult<Vec<_>>>()?;
        let members = node
            .members
            .iter()
            .map(|m| self.visit_function_item(m))
            .collect::<HirResult<Vec<_>>>()?;
        let instance = HirInstance {
            span: node.span,
            name,
            instantiation_type_parameters,
            members,
        };
        Ok(instance)
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
    pub fn visit_type_item(&mut self, node: &'ast AstTypeItem) -> HirResult<HirRecord<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let fields = node
            .members
            .iter()
            .map(|member| {
                let ty = self.visit_type(&member.ty)?;
                let field = HirRecordField {
                    name: self.visit_identifier(&member.name)?,
                    ty,
                    type_annotation: *member.ty.span(),
                    span: member.span,
                };
                Ok((member.name.name.to_owned(), field))
            })
            .collect::<HirResult<BTreeMap<_, _>>>()?;
        let rec = HirRecord {
            name,
            fields,
            span: node.span,
        };
        Ok(rec)
    }

    pub fn visit_stmt(&mut self, node: &'ast AstStmt) -> HirResult<HirStmt<'ta>> {
        match node {
            AstStmt::Let(s) => self.visit_let_stmt(s),
            AstStmt::Return(s) => self.visit_return_stmt(s),
            AstStmt::For(s) => self.visit_for_stmt(s),
            AstStmt::Break(s) => self.visit_break_stmt(s),
            AstStmt::Continue(s) => self.visit_continue_stmt(s),
            AstStmt::If(s) => self.visit_if_stmt(s),
            AstStmt::Expr(s) => self.visit_expr_stmt(s),
        }
    }

    pub fn visit_let_stmt(&mut self, node: &'ast AstLetStmt) -> HirResult<HirStmt<'ta>> {
        let name = self.visit_identifier(&node.name)?;
        let ty = match &node.ty {
            Some(t) => self.visit_type(t)?,
            None => self.arena.get_uninitialized_ty(),
        };
        let value = self.visit_expr(&node.value)?;
        let hir = HirStmt::Let(HirLetStmt {
            span: node.span,
            name,
            ty,
            type_annotation: node.ty.as_ref().map(|t| *t.span()),
            value,
        });
        Ok(hir)
    }

    pub fn visit_return_stmt(&mut self, node: &'ast AstReturnStmt) -> HirResult<HirStmt<'ta>> {
        let value = node
            .value
            .as_ref()
            .map(|v| self.visit_expr(v))
            .transpose()?;
        let hir = HirStmt::Return(HirReturnStmt {
            span: node.span,
            value,
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
    pub fn visit_for_stmt(&mut self, node: &'ast AstForStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth.push_back(node);
        // Build the let statement for the initializer
        let initializer = node
            .initializer
            .as_ref()
            .map(|i| -> HirResult<HirLetStmt> {
                Ok(HirLetStmt {
                    span: i.span,
                    name: self.visit_identifier(&i.name)?,
                    ty: self.arena.get_uninitialized_ty(),
                    type_annotation: None,
                    value: self.visit_expr(&i.initializer)?,
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
            span: node.span,
            body: vec![
                Box::new(initializer.map(HirStmt::Let).unwrap_or_else(|| {
                    HirStmt::Block(HirBlockStmt {
                        span: Span::empty(),
                        body: vec![],
                    })
                })),
                Box::new(HirStmt::Loop(HirLoopStmt {
                    span: node.span,
                    condition,
                    body: {
                        let mut stmts = body;
                        if let Some(i) = increment {
                            stmts.push(HirStmt::Expr(HirExprStmt {
                                span: *i.span(),
                                expr: i,
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
    pub fn visit_if_stmt(&mut self, node: &'ast AstIfStmt) -> HirResult<HirStmt<'ta>> {
        let condition = self.visit_expr(&node.condition)?;
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
            span: node.span,
            condition,
            happy_path,
            unhappy_path,
        });
        Ok(hir)
    }

    pub fn visit_break_stmt(&mut self, node: &'ast AstBreakStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .back()
            .ok_or(HirError::BreakOutsideLoop(BreakOutsideLoopError {
                span: node.span,
            }))?;
        let hir = HirStmt::Break(HirBreakStmt { span: node.span });
        Ok(hir)
    }

    pub fn visit_expr_stmt(&mut self, node: &'ast AstExprStmt) -> HirResult<HirStmt<'ta>> {
        let expr = self.visit_expr(&node.expr)?;
        let hir = HirStmt::Expr(HirExprStmt {
            span: node.span,
            expr,
        });
        Ok(hir)
    }

    pub fn visit_continue_stmt(&mut self, node: &'ast AstContinueStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .back()
            .ok_or(HirError::ContinueOutsideLoop(ContinueOutsideLoopError {
                span: node.span,
            }))?;
        let hir = HirStmt::Continue(HirContinueStmt { span: node.span });
        Ok(hir)
    }

    /// Translate a syntax identifier into a HIR name.
    pub fn visit_identifier(&mut self, node: &AstIdentifier) -> HirResult<HirName> {
        Ok(HirName {
            name: node.name.to_owned(),
            span: node.span,
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
    pub fn visit_type(&mut self, node: &AstType) -> HirResult<&'ta HirTy<'ta>> {
        let ty = match node {
            AstType::Unit(_) => self.arena.get_unit_ty(),
            AstType::Integer32(_) => self.arena.get_integer32_ty(),
            AstType::Boolean(_) => self.arena.get_boolean_ty(),
            AstType::Named(t) => self.arena.get_nominal_ty(&self.visit_identifier(&t.name)?),
            AstType::Pointer(t) => self
                .arena
                .get_pointer_ty(self.visit_type(t.inner.as_ref())?),
        };
        Ok(ty)
    }
}
