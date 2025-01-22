use crate::error::{
    BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult, UnknownIntrinsicTypeError,
};
use crate::HirBuilder;
use eight_diagnostics::ice;
use eight_middle::context::CompileContext;
use eight_middle::hir::expr::{HirBinaryOp, HirConstructExprArgument, HirExpr, HirUnaryOp};
use eight_middle::hir::item::{HirFunction, HirInstance, HirStruct, HirTrait, HirType};
use eight_middle::hir::module::{HirModule, HirModuleBody};
use eight_middle::hir::signature::{
    HirFunctionParameterSignature, HirFunctionSignature, HirInstanceSignature, HirModuleSignature,
    HirStructFieldSignature, HirStructSignature, HirTraitSignature, HirTypeParameterSignature,
    HirTypeSignature,
};
use eight_middle::hir::stmt::{HirExprStmt, HirLetStmt, HirStmt};
use eight_middle::hir::ty::HirTy;
use eight_middle::scope::Scope;
use eight_middle::LinkageType;
use eight_span::Span;
use eight_syntax::ast::{
    AstAssignExpr, AstBinaryOp, AstBinaryOpExpr, AstBooleanLiteralExpr, AstBracketIndexExpr,
    AstBreakStmt, AstCallExpr, AstConstructExpr, AstConstructorExprArgument, AstContinueStmt,
    AstDotIndexExpr, AstExpr, AstExprStmt, AstForStmt, AstFunctionItem, AstFunctionParameterItem,
    AstGroupExpr, AstIfStmt, AstInstanceItem, AstIntegerLiteralExpr, AstItem, AstLetStmt,
    AstReferenceExpr, AstReturnStmt, AstStmt, AstStructItem, AstTraitFunctionItem, AstTraitItem,
    AstTranslationUnit, AstType, AstTypeItem, AstTypeParameterItem, AstUnaryOp, AstUnaryOpExpr,
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
pub struct AstSyntaxLoweringPass<'ast, 'hir> {
    cc: &'hir CompileContext<'hir>,
    loop_depth: VecDeque<&'ast AstForStmt<'ast>>,

    /// When traversing the AST, we replace any generic syntax with De Bruijn indexed type
    /// variables.
    ///
    /// These differ from the meta variables used in unification.
    type_binding_context: Scope<&'hir str, &'hir HirTy<'hir>>,
    type_binding_depth: u32,
    type_binding_index: u32,
}

impl<'ast, 'hir> AstSyntaxLoweringPass<'ast, 'hir> {
    pub fn new(cc: &'hir CompileContext<'hir>) -> Self {
        Self {
            cc,
            loop_depth: VecDeque::new(),
            type_binding_context: Scope::default(),
            type_binding_depth: 0,
            type_binding_index: 0,
        }
    }

    /// Enter a new type binding scope.
    ///
    /// This is only to be used for generic type parameter boundaries, such as entering a function
    /// with generic type parameters, or the body of a trait.
    pub fn enter_type_binding_scope(&mut self) {
        self.type_binding_depth += 1;
        self.type_binding_index = 0;
        self.type_binding_context.enter_scope();
    }

    /// Leave the current type binding scope.
    pub fn leave_type_binding_scope(&mut self) {
        self.type_binding_context.leave_scope();
        self.type_binding_depth -= 1;
        self.type_binding_index = 0;
    }

    pub fn record_typ_binding(&mut self, name: &'hir str, ty: &'hir HirTy<'hir>) -> HirResult<()> {
        self.type_binding_context.add(name, ty);
        Ok(())
    }

    pub fn find_type_binding(&self, name: &'hir str) -> Option<&'hir HirTy<'hir>> {
        self.type_binding_context.find(&name).copied()
    }

    pub fn fresh_type_variable(&mut self) -> &'hir HirTy<'hir> {
        let depth = self.type_binding_depth;
        let index = self.type_binding_index;
        let ty = self.cc.hir_variable_type(depth, index);
        self.type_binding_index += 1;
        ty
    }

    /// Helper function to drain a set of [`AstTypeParameterItem`] into the current binding context.
    pub fn drain_type_parameters(&mut self, tys: &[&AstTypeParameterItem]) {
        for ty in tys {
            let type_variable = self.fresh_type_variable();
            let key = self.cc.intern_str(&ty.name.name);
            self.type_binding_context.add(key, type_variable);
        }
    }
}

impl<'ast, 'hir> AstSyntaxLoweringPass<'ast, 'hir> {
    pub fn visit_expr(&mut self, node: &'ast AstExpr) -> HirResult<HirExpr<'hir>> {
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

    pub fn visit_assign_expr(&mut self, node: &'ast AstAssignExpr) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::Assign(HirBuilder::build_assign_expr(
            node.span,
            self.visit_expr(node.lhs)?,
            self.visit_expr(node.rhs)?,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_call_expr(&mut self, node: &'ast AstCallExpr) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::Call(HirBuilder::build_call_expr(
            node.span,
            self.visit_expr(node.callee)?,
            HirBuilder::build_vec(node.arguments.iter(), |a| self.visit_expr(a))?,
            node.type_arguments
                .iter()
                .map(|t| self.visit_type(t))
                .collect::<HirResult<Vec<_>>>()?,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_construct_expr(
        &mut self,
        node: &'ast AstConstructExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::Construct(HirBuilder::build_construct_expr(
            node.span,
            self.visit_type(node.callee)?,
            HirBuilder::build_vec(node.arguments.iter(), |a| {
                self.visit_constructor_expr_argument(a)
            })?,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_constructor_expr_argument(
        &mut self,
        node: &'ast AstConstructorExprArgument,
    ) -> HirResult<HirConstructExprArgument<'hir>> {
        Ok(HirBuilder::build_construct_expr_argument(
            node.span,
            self.cc.intern_str(&node.field.name),
            node.field.span,
            self.visit_expr(node.expr)?,
        ))
    }

    pub fn visit_group_expr(&mut self, node: &'ast AstGroupExpr) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::Group(HirBuilder::build_group_expr(
            node.span,
            self.visit_expr(node.inner)?,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        node: &'ast AstIntegerLiteralExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::IntegerLiteral(
            HirBuilder::build_integer_literal_expr(
                node.span,
                node.value,
                self.cc.hir_uninitialized_type(),
            ),
        ))
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        node: &'ast AstBooleanLiteralExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::BooleanLiteral(
            HirBuilder::build_boolean_literal_expr(
                node.span,
                node.value,
                self.cc.hir_uninitialized_type(),
            ),
        ))
    }

    /// Visit a unary operator expression.
    ///
    /// We translate the AddressOf and Deref operators into separate expressions, as they produce
    /// different types
    pub fn visit_unary_op_expr(&mut self, node: &'ast AstUnaryOpExpr) -> HirResult<HirExpr<'hir>> {
        match &node.op {
            AstUnaryOp::Not | AstUnaryOp::Neg => {
                Ok(HirExpr::UnaryOp(HirBuilder::build_unary_op_expr(
                    node.span,
                    self.visit_expr(node.operand)?,
                    self.visit_unary_op(&node.op)?,
                    node.op_span,
                    self.cc.hir_uninitialized_type(),
                )))
            }
            AstUnaryOp::Deref => Ok(HirExpr::Deref(HirBuilder::build_deref_expr(
                node.span,
                self.visit_expr(node.operand)?,
                self.cc.hir_uninitialized_type(),
            ))),
            AstUnaryOp::AddressOf => Ok(HirExpr::AddressOf(HirBuilder::build_address_of_expr(
                node.span,
                self.visit_expr(node.operand)?,
                self.cc.hir_uninitialized_type(),
            ))),
        }
    }

    pub fn visit_binary_op_expr(
        &mut self,
        node: &'ast AstBinaryOpExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::BinaryOp(HirBuilder::build_binary_op_expr(
            node.span,
            self.visit_expr(node.lhs)?,
            self.visit_expr(node.rhs)?,
            self.visit_binary_op(&node.op)?,
            node.op_span,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_dot_index_expr(
        &mut self,
        node: &'ast AstDotIndexExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::ConstantIndex(
            HirBuilder::build_constant_index_expr(
                node.span,
                self.visit_expr(node.origin)?,
                self.cc.intern_str(&node.index.name),
                node.index.span,
                self.cc.hir_uninitialized_type(),
            ),
        ))
    }

    pub fn visit_bracket_index_expr(
        &mut self,
        node: &'ast AstBracketIndexExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::OffsetIndex(HirBuilder::build_offset_index_expr(
            node.span,
            self.visit_expr(node.origin)?,
            self.visit_expr(node.index)?,
            self.cc.hir_uninitialized_type(),
        )))
    }

    pub fn visit_reference_expr(
        &mut self,
        node: &'ast AstReferenceExpr,
    ) -> HirResult<HirExpr<'hir>> {
        Ok(HirExpr::Reference(HirBuilder::build_reference_expr(
            node.span,
            self.cc.intern_str(&node.name.name),
            node.name.span,
            self.cc.hir_uninitialized_type(),
        )))
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
            AstBinaryOp::Lte => Ok(HirBinaryOp::Lte),
            AstBinaryOp::Gte => Ok(HirBinaryOp::Gte),
            AstBinaryOp::And => Ok(HirBinaryOp::And),
            AstBinaryOp::Or => Ok(HirBinaryOp::Or),
        }
    }

    pub fn visit_translation_unit(
        &mut self,
        node: &'ast AstTranslationUnit,
    ) -> HirResult<HirModule<'hir>> {
        let mut module_body = HirModuleBody::default();
        let mut module_signature = HirModuleSignature::default();

        for item in node.items {
            self.visit_item(&mut module_body, &mut module_signature, item)?;
        }

        // We can now intern the module signature since it is immutable
        Ok(HirModule::new(
            self.cc.arena_alloc(module_signature),
            module_body,
        ))
    }

    /// Visit an item in the module.
    ///
    /// The syntax lowering pass synthesizes intrinsic functions into regular functions with the
    /// linkage type marked external.
    pub fn visit_item(
        &mut self,
        module_body: &mut HirModuleBody<'hir>,
        module_signature: &mut HirModuleSignature<'hir>,
        node: &'ast AstItem,
    ) -> HirResult<()> {
        match node {
            AstItem::Function(f) => {
                let fun = self.visit_function_item(f)?;
                let name = self.cc.intern_str(&f.name.name);
                module_signature.add_function(name, fun.signature);
                module_body.functions.insert(name, fun);
            }
            AstItem::Struct(t) => {
                let r#struct = self.visit_struct_item(t)?;
                let name = self.cc.intern_str(&t.name.name);
                module_signature.add_struct(name, r#struct.signature);
                module_body.structs.insert(name, r#struct);
            }
            AstItem::Type(s) => {
                let r#type = self.visit_type_item(s)?;
                let name = self.cc.intern_str(&s.name.name);
                module_signature.add_type(name, r#type.signature);
                module_body.types.insert(name, r#type);
            }
            AstItem::Trait(t) => {
                let r#trait = self.visit_trait_item(t)?;
                let name = self.cc.intern_str(&t.name.name);
                module_signature.add_trait(name, r#trait.signature);
                module_body.traits.insert(name, r#trait);
            }
            AstItem::Instance(i) => {
                let instance = self.visit_instance_item(i)?;
                module_signature.add_instance(instance.signature);
                module_body.instances.push(instance);
            }
        };
        Ok(())
    }

    pub fn visit_function_item(
        &mut self,
        node: &'ast AstFunctionItem,
    ) -> HirResult<HirFunction<'hir>> {
        self.enter_type_binding_scope();
        self.drain_type_parameters(node.type_parameters.iter().as_slice());

        let type_parameters = HirBuilder::build_vec(node.type_parameters.iter(), |p| {
            self.visit_type_parameter_item(p)
        })?;
        let return_type_annotation = node.return_type.map(|t| t.span());
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.cc.hir_unit_type(),
        };
        let parameters =
            HirBuilder::build_vec(node.parameters.iter(), |p| self.visit_function_parameter(p))?;
        let body = HirBuilder::build_vec(node.body.iter(), |stmt| self.visit_stmt(stmt))?;
        let signature = self.cc.arena_alloc(HirFunctionSignature {
            span: node.span,
            parameters,
            type_parameters,
            return_type,
            return_type_annotation,
        });
        let linkage_type = if node.is_intrinsic {
            LinkageType::External
        } else {
            LinkageType::Eight
        };
        self.leave_type_binding_scope();
        Ok(HirBuilder::build_function(
            node.span,
            self.cc.intern_str(&node.name.name),
            node.name.span,
            signature,
            body,
            linkage_type,
        ))
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &'ast AstFunctionParameterItem,
    ) -> HirResult<&'hir HirFunctionParameterSignature<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let ty = self.visit_type(node.ty)?;
        let hir = self.cc.arena_alloc(HirFunctionParameterSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            ty,
            ty_annotation: node.ty.span(),
        });
        Ok(hir)
    }

    pub fn visit_type_parameter_item(
        &mut self,
        node: &'ast AstTypeParameterItem,
    ) -> HirResult<&'hir HirTypeParameterSignature<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let key = self.cc.intern_str(&node.name.name);
        let ty = self
            .find_type_binding(key)
            .unwrap_or_else(|| ice!("failed to find allocated type"));
        let hir = self.cc.arena_alloc(HirTypeParameterSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            ty,
        });
        Ok(hir)
    }

    pub fn visit_type_item(&mut self, node: &'ast AstTypeItem) -> HirResult<HirType<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let signature = self.cc.arena_alloc(HirTypeSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            ty: match node.name.name.as_str() {
                "i32" => self.cc.hir_integer32_type(),
                "bool" => self.cc.hir_boolean_type(),
                "unit" => self.cc.hir_unit_type(),
                _ => {
                    return Err(HirError::UnknownIntrinsicType(UnknownIntrinsicTypeError {
                        name: node.name.name.to_owned(),
                        span: node.name.span,
                    }))
                }
            },
        });
        let r#type = HirType {
            span: node.span,
            name,
            name_span: node.name.span,
            signature,
        };
        Ok(r#type)
    }

    pub fn visit_trait_item(&mut self, node: &'ast AstTraitItem) -> HirResult<HirTrait<'hir>> {
        self.enter_type_binding_scope();
        self.drain_type_parameters(node.type_parameters.iter().as_slice());

        let name = self.cc.intern_str(&node.name.name);
        let type_parameters = HirBuilder::build_vec(node.type_parameters.iter(), |p| {
            self.visit_type_parameter_item(p)
        })?;
        let mut members = BTreeMap::new();
        for member in node.members.iter() {
            let signature = self.visit_trait_function_item(member)?;
            let name = self.cc.intern_str(&member.name.name);
            members.insert(name, signature);
        }
        let signature = self.cc.arena_alloc(HirTraitSignature {
            span: node.span,
            type_parameters,
            name,
            name_span: node.name.span,
            methods: members,
        });
        self.leave_type_binding_scope();
        Ok(HirBuilder::build_trait(
            node.span,
            self.cc.intern_str(&node.name.name),
            node.name.span,
            signature,
        ))
    }

    pub fn visit_trait_function_item(
        &mut self,
        node: &'ast AstTraitFunctionItem,
    ) -> HirResult<&'hir HirFunctionSignature<'hir>> {
        self.enter_type_binding_scope();
        self.drain_type_parameters(node.type_parameters.iter().as_slice());

        let type_parameters = HirBuilder::build_vec(node.type_parameters.iter(), |p| {
            self.visit_type_parameter_item(p)
        })?;
        let parameters =
            HirBuilder::build_vec(node.parameters.iter(), |p| self.visit_function_parameter(p))?;
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.cc.hir_unit_type(),
        };
        let return_type_annotation = node.return_type.map(|t| t.span());
        let signature = self.cc.arena_alloc(HirFunctionSignature {
            span: node.span,
            parameters,
            type_parameters,
            return_type,
            return_type_annotation,
        });

        self.leave_type_binding_scope();
        Ok(signature)
    }

    pub fn visit_instance_item(
        &mut self,
        node: &'ast AstInstanceItem,
    ) -> HirResult<HirInstance<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let type_arguments =
            HirBuilder::build_vec(node.instantiation_type_parameters.iter(), |t| {
                self.visit_type(t)
            })?;
        let members = HirBuilder::build_vec(node.members.iter(), |m| self.visit_function_item(m))?;
        let signature = self.cc.arena_alloc(HirInstanceSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            type_arguments: type_arguments.clone(),
            trait_name: name,
            trait_name_span: node.name.span,
            methods: members.iter().map(|m| (m.name, m.signature)).collect(),
        });
        Ok(HirBuilder::build_instance(
            node.span,
            self.cc.intern_str(&node.name.name),
            node.name.span,
            type_arguments,
            members,
            signature,
        ))
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
    pub fn visit_struct_item(&mut self, node: &'ast AstStructItem) -> HirResult<HirStruct<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let mut fields = BTreeMap::new();
        for member in node.members.iter() {
            let ty = self.visit_type(member.ty)?;
            let field = self.cc.arena_alloc(HirStructFieldSignature {
                span: member.span,
                name: self.cc.intern_str(&member.name.name),
                name_span: member.name.span,
                ty,
                ty_annotation: member.ty.span(),
            });
            let field_name = self.cc.intern_str(&member.name.name);
            fields.insert(field_name, field);
        }
        let signature = self.cc.arena_alloc(HirStructSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            fields,
        });
        let rec = HirStruct {
            name,
            name_span: node.name.span,
            span: node.span,
            signature,
            instantiated_fields: BTreeMap::new(),
        };
        Ok(rec)
    }

    pub fn visit_stmt(&mut self, node: &'ast AstStmt) -> HirResult<HirStmt<'hir>> {
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

    pub fn visit_let_stmt(&mut self, node: &'ast AstLetStmt) -> HirResult<HirStmt<'hir>> {
        let name = self.cc.intern_str(&node.name.name);
        let ty = match &node.ty {
            Some(t) => self.visit_type(t)?,
            None => self.cc.hir_uninitialized_type(),
        };
        let value = self.visit_expr(node.value)?;
        Ok(HirStmt::Let(HirBuilder::build_let_stmt(
            node.span,
            name,
            node.name.span,
            ty,
            node.ty.map(|t| t.span()),
            value,
        )))
    }

    pub fn visit_return_stmt(&mut self, node: &'ast AstReturnStmt) -> HirResult<HirStmt<'hir>> {
        let value = node.value.map(|v| self.visit_expr(v)).transpose()?;
        Ok(HirStmt::Return(HirBuilder::build_return_stmt(
            node.span, value,
        )))
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
    pub fn visit_for_stmt(&mut self, node: &'ast AstForStmt) -> HirResult<HirStmt<'hir>> {
        self.loop_depth.push_back(node);
        // Build the let statement for the initializer
        let initializer = node
            .initializer
            .map(|i| -> HirResult<HirLetStmt> {
                Ok(HirBuilder::build_let_stmt(
                    i.span,
                    self.cc.intern_str(&i.name.name),
                    i.name.span,
                    self.cc.hir_uninitialized_type(),
                    None,
                    self.visit_expr(i.initializer)?,
                ))
            })
            .transpose()?;
        // Take the condition, or insert a `true` literal node
        let condition = node
            .condition
            .map(|c| self.visit_expr(c))
            .transpose()?
            .unwrap_or_else(|| {
                HirExpr::BooleanLiteral(HirBuilder::build_boolean_literal_expr(
                    // TODO: Should this span actually be empty? Probably?
                    Span::empty(),
                    true,
                    self.cc.hir_uninitialized_type(),
                ))
            });
        let increment = node.increment.map(|i| self.visit_expr(i)).transpose()?;
        let body = HirBuilder::build_vec(node.body.iter(), |stmt| self.visit_stmt(stmt))?;
        // Build the new block statement with the loop
        let hir = HirStmt::Block(HirBuilder::build_block_stmt(
            node.span,
            vec![
                initializer.map(HirStmt::Let).unwrap_or_else(|| {
                    HirStmt::Block(HirBuilder::build_block_stmt(Span::empty(), vec![]))
                }),
                HirStmt::Loop(HirBuilder::build_loop_stmt(node.span, condition, {
                    let mut stmts = body;
                    if let Some(i) = increment {
                        stmts.push(HirStmt::Expr(HirExprStmt {
                            span: i.span(),
                            expr: i,
                        }));
                    }
                    stmts
                })),
            ],
        ));
        self.loop_depth.pop_back();
        Ok(hir)
    }

    /// Translate an if statement into a conditional expression.
    ///
    /// The synthesis of the if statement simply replaces a missing unhappy path with an empty
    /// block.
    pub fn visit_if_stmt(&mut self, node: &'ast AstIfStmt) -> HirResult<HirStmt<'hir>> {
        let condition = self.visit_expr(node.condition)?;
        let happy_path = HirBuilder::build_vec(node.happy_path.iter(), |s| self.visit_stmt(s))?;
        let unhappy_path = match &node.unhappy_path {
            Some(unhappy_path) => {
                HirBuilder::build_vec(unhappy_path.iter(), |s| self.visit_stmt(s))?
            }
            None => vec![],
        };
        Ok(HirStmt::If(HirBuilder::build_if_stmt(
            node.span,
            condition,
            happy_path,
            unhappy_path,
        )))
    }

    pub fn visit_break_stmt(&mut self, node: &'ast AstBreakStmt) -> HirResult<HirStmt<'hir>> {
        self.loop_depth
            .back()
            .ok_or(HirError::BreakOutsideLoop(BreakOutsideLoopError {
                span: node.span,
            }))?;
        Ok(HirStmt::Break(HirBuilder::build_break_stmt(node.span)))
    }

    pub fn visit_continue_stmt(&mut self, node: &'ast AstContinueStmt) -> HirResult<HirStmt<'hir>> {
        self.loop_depth
            .back()
            .ok_or(HirError::ContinueOutsideLoop(ContinueOutsideLoopError {
                span: node.span,
            }))?;
        Ok(HirStmt::Continue(HirBuilder::build_continue_stmt(
            node.span,
        )))
    }

    pub fn visit_expr_stmt(&mut self, node: &'ast AstExprStmt) -> HirResult<HirStmt<'hir>> {
        let expr = self.visit_expr(node.expr)?;
        Ok(HirStmt::Expr(HirBuilder::build_expr_stmt(node.span, expr)))
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
    pub fn visit_type(&mut self, node: &'ast AstType) -> HirResult<&'hir HirTy<'hir>> {
        let ty = match node {
            AstType::Unit(_) => self.cc.hir_unit_type(),
            AstType::Integer32(_) => self.cc.hir_integer32_type(),
            AstType::Boolean(_) => self.cc.hir_boolean_type(),
            AstType::Named(t) => {
                let key = self.cc.intern_str(&t.name.name);
                match self.find_type_binding(key) {
                    Some(ty) => ty,
                    _ => self
                        .cc
                        .hir_nominal_type(self.cc.intern_str(&t.name.name), t.name.span),
                }
            }
            AstType::Pointer(t) => self.cc.hir_pointer_type(self.visit_type(t.inner)?),
        };
        Ok(ty)
    }
}
