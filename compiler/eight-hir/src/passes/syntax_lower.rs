use crate::arena::HirArena;
use crate::error::{
    BreakOutsideLoopError, ContinueOutsideLoopError, HirError, HirResult, UnknownIntrinsicTypeError,
};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use crate::item::{HirFunction, HirInstance, HirIntrinsicType, HirStruct, HirTrait};
use crate::signature::{
    HirFunctionApiSignature, HirFunctionParameterApiSignature, HirInstanceApiSignature,
    HirModuleSignature, HirStructApiSignature, HirStructFieldApiSignature, HirTraitApiSignature,
    HirTypeApiSignature, HirTypeParameterApiSignature,
};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::HirTy;
use crate::{HirModule, HirModuleBody, LinkageType};
use eight_diagnostics::ice;
use eight_span::Span;
use eight_syntax::ast::{
    AstAssignExpr, AstBinaryOp, AstBinaryOpExpr, AstBooleanLiteralExpr, AstBracketIndexExpr,
    AstBreakStmt, AstCallExpr, AstConstructExpr, AstConstructorExprArgument, AstContinueStmt,
    AstDotIndexExpr, AstExpr, AstExprStmt, AstForStmt, AstFunctionItem, AstFunctionParameterItem,
    AstGroupExpr, AstIfStmt, AstInstanceItem, AstIntegerLiteralExpr, AstIntrinsicFunctionItem,
    AstIntrinsicTypeItem, AstItem, AstLetStmt, AstReferenceExpr, AstReturnStmt, AstStmt,
    AstStructItem, AstTraitFunctionItem, AstTraitItem, AstTranslationUnit, AstType,
    AstTypeParameterItem, AstUnaryOp, AstUnaryOpExpr,
};
use std::cell::RefCell;
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
    loop_depth: RefCell<VecDeque<&'ast AstForStmt<'ast>>>,
}

impl<'ast, 'ta> ASTSyntaxLoweringPass<'ast, 'ta> {
    pub fn new(arena: &'ta HirArena<'ta>) -> Self {
        Self {
            arena,
            loop_depth: RefCell::new(VecDeque::new()),
        }
    }
}

impl<'ast, 'ta> ASTSyntaxLoweringPass<'ast, 'ta> {
    pub fn visit_expr(&'ta self, node: &'ast AstExpr) -> HirResult<HirExpr<'ta>> {
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

    pub fn visit_assign_expr(&'ta self, node: &'ast AstAssignExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Assign(HirAssignExpr {
            span: node.span,
            lhs: Box::new(self.visit_expr(node.lhs)?),
            rhs: Box::new(self.visit_expr(node.rhs)?),
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_call_expr(&'ta self, node: &'ast AstCallExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Call(HirCallExpr {
            span: node.span,
            callee: Box::new(self.visit_expr(node.callee)?),
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
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_construct_expr(
        &'ta self,
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
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_constructor_expr_argument(
        &'ta self,
        node: &'ast AstConstructorExprArgument,
    ) -> HirResult<HirConstructExprArgument<'ta>> {
        let hir = HirConstructExprArgument {
            span: node.span,
            field: self.arena.names().get(&node.field.name),
            field_span: node.field.span,
            expr: Box::new(self.visit_expr(&node.expr)?),
        };
        Ok(hir)
    }

    pub fn visit_group_expr(&'ta self, node: &'ast AstGroupExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Group(HirGroupExpr {
            span: node.span,
            inner: Box::new(self.visit_expr(node.inner)?),
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_integer_literal_expr(
        &'ta self,
        node: &'ast AstIntegerLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::IntegerLiteral(HirIntegerLiteralExpr {
            span: node.span,
            value: node.value,
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_boolean_literal_expr(
        &'ta self,
        node: &'ast AstBooleanLiteralExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
            span: node.span,
            value: node.value,
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    /// Visit a unary operator expression.
    ///
    /// We translate the AddressOf and Deref operators into separate expressions, as they produce
    /// different types
    pub fn visit_unary_op_expr(&'ta self, node: &'ast AstUnaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = match &node.op {
            AstUnaryOp::Not | AstUnaryOp::Neg => HirExpr::UnaryOp(HirUnaryOpExpr {
                span: node.span,
                operand: Box::new(self.visit_expr(node.operand)?),
                op: self.visit_unary_op(&node.op)?,
                op_span: node.op_span,
                ty: self.arena.types().get_uninitialized_ty(),
            }),
            AstUnaryOp::Deref => HirExpr::Deref(HirDerefExpr {
                span: node.span,
                inner: Box::new(self.visit_expr(node.operand)?),
                ty: self.arena.types().get_uninitialized_ty(),
            }),
            AstUnaryOp::AddressOf => HirExpr::AddressOf(HirAddressOfExpr {
                span: node.span,
                inner: Box::new(self.visit_expr(node.operand)?),
                ty: self.arena.types().get_uninitialized_ty(),
            }),
        };
        Ok(hir)
    }

    pub fn visit_binary_op_expr(&'ta self, node: &'ast AstBinaryOpExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::BinaryOp(HirBinaryOpExpr {
            span: node.span,
            lhs: Box::new(self.visit_expr(node.lhs)?),
            rhs: Box::new(self.visit_expr(node.rhs)?),
            op: self.visit_binary_op(&node.op)?,
            op_span: node.op_span,
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_dot_index_expr(&'ta self, node: &'ast AstDotIndexExpr) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::ConstantIndex(HirConstantIndexExpr {
            span: node.span,
            origin: Box::new(self.visit_expr(node.origin)?),
            index: self.arena.names().get(&node.index.name),
            index_span: node.index.span,
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_bracket_index_expr(
        &'ta self,
        node: &'ast AstBracketIndexExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::OffsetIndex(HirOffsetIndexExpr {
            span: node.span,
            origin: Box::new(self.visit_expr(node.origin)?),
            index: Box::new(self.visit_expr(node.index)?),
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_reference_expr(
        &'ta self,
        node: &'ast AstReferenceExpr,
    ) -> HirResult<HirExpr<'ta>> {
        let hir = HirExpr::Reference(HirReferenceExpr {
            span: node.span,
            name: self.arena.names().get(&node.name.name),
            name_span: node.name.span,
            ty: self.arena.types().get_uninitialized_ty(),
        });
        Ok(hir)
    }

    pub fn visit_unary_op(&'ta self, node: &'ast AstUnaryOp) -> HirResult<HirUnaryOp> {
        match node {
            AstUnaryOp::Not => Ok(HirUnaryOp::Not),
            AstUnaryOp::Neg => Ok(HirUnaryOp::Neg),
            _ => ice!("visit_unary_op called addressof or deref operator"),
        }
    }

    pub fn visit_binary_op(&'ta self, node: &'ast AstBinaryOp) -> HirResult<HirBinaryOp> {
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
        &'ta self,
        node: &'ast AstTranslationUnit,
    ) -> HirResult<HirModule<'ta>> {
        let mut module_body = HirModuleBody::default();
        let mut module_signature = HirModuleSignature::default();

        for item in node.items {
            self.visit_item(&mut module_body, &mut module_signature, item)?;
        }

        // We can now intern the module signature since it is immutable
        Ok(HirModule::new(
            self.arena.intern(module_signature),
            module_body,
        ))
    }

    /// Visit an item in the module.
    ///
    /// The syntax lowering pass synthesizes intrinsic functions into regular functions with the
    /// linkage type marked external.
    pub fn visit_item(
        &'ta self,
        module_body: &mut HirModuleBody<'ta>,
        module_signature: &mut HirModuleSignature<'ta>,
        node: &'ast AstItem,
    ) -> HirResult<()> {
        match node {
            AstItem::Function(f) => {
                let fun = self.visit_function_item(f)?;
                let name = self.arena.names().get(&f.name.name);
                module_signature.add_function(name, fun.signature);
                module_body.functions.insert(name, fun);
            }
            AstItem::IntrinsicFunction(f) => {
                let fun = self.visit_intrinsic_function_item(f)?;
                let name = self.arena.names().get(&f.name.name);
                module_signature.add_function(name, fun.signature);
                module_body.functions.insert(name, fun);
            }
            AstItem::Struct(t) => {
                let r#struct = self.visit_type_item(t)?;
                let name = self.arena.names().get(&t.name.name);
                module_signature.add_struct(name, r#struct.signature);
                module_body.structs.insert(name, r#struct);
            }
            AstItem::IntrinsicType(s) => {
                let r#type = self.visit_intrinsic_type_item(s)?;
                let name = self.arena.names().get(&s.name.name);
                module_signature.add_type(name, r#type.signature);
                module_body.types.insert(name, r#type);
            }
            AstItem::Trait(t) => {
                let r#trait = self.visit_trait_item(t)?;
                let name = self.arena.names().get(&t.name.name);
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
        &'ta self,
        node: &'ast AstFunctionItem,
    ) -> HirResult<HirFunction<'ta>> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parameter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = node.return_type.as_ref().map(|t| *t.span());
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.arena.types().get_unit_ty(),
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
        let signature = self.arena.intern(HirFunctionApiSignature {
            span: node.span,
            parameters,
            type_parameters,
            return_type,
            return_type_annotation,
        });
        let fun = HirFunction {
            span: node.span,
            name: self.arena.names().get(&node.name.name),
            name_span: node.name.span,
            signature,
            body,
            type_parameter_substitutions: BTreeMap::new(),
            instantiated_parameters: BTreeMap::new(),
            instantiated_return_type: None,
            linkage_type: LinkageType::Eight,
        };
        Ok(fun)
    }

    pub fn visit_intrinsic_function_item(
        &'ta self,
        node: &'ast AstIntrinsicFunctionItem,
    ) -> HirResult<HirFunction<'ta>> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parameter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type_annotation = *node.return_type.span();
        let return_type = self.visit_type(&node.return_type)?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let signature = self.arena.intern(HirFunctionApiSignature {
            span: node.span,
            parameters,
            type_parameters,
            return_type,
            return_type_annotation: Some(return_type_annotation),
        });
        let fun = HirFunction {
            span: node.span,
            name: self.arena.names().get(&node.name.name),
            name_span: node.name.span,
            signature,
            body: Vec::new(),
            type_parameter_substitutions: BTreeMap::new(),
            instantiated_parameters: BTreeMap::new(),
            instantiated_return_type: None,
            linkage_type: LinkageType::External,
        };
        Ok(fun)
    }

    pub fn visit_function_parameter(
        &'ta self,
        node: &'ast AstFunctionParameterItem,
    ) -> HirResult<&'ta HirFunctionParameterApiSignature<'ta>> {
        let name = self.arena.names().get(&node.name.name);
        let ty = self.visit_type(&node.ty)?;
        let hir = self.arena.intern(HirFunctionParameterApiSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            ty,
            ty_annotation: *node.ty.span(),
        });
        Ok(hir)
    }

    pub fn visit_type_parameter_item(
        &'ta self,
        node: &'ast AstTypeParameterItem,
    ) -> HirResult<&'ta HirTypeParameterApiSignature> {
        let name = self.arena.names().get(&node.name.name);
        let hir = self.arena.intern(HirTypeParameterApiSignature {
            span: node.span,
            name,
            name_span: node.name.span,
        });
        Ok(hir)
    }

    pub fn visit_intrinsic_type_item(
        &'ta self,
        node: &'ast AstIntrinsicTypeItem,
    ) -> HirResult<HirIntrinsicType<'ta>> {
        let name = self.arena.names().get(&node.name.name);
        let signature = self.arena.intern(HirTypeApiSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            ty: match node.name.name.as_str() {
                "i32" => self.arena.types().get_integer32_ty(),
                "bool" => self.arena.types().get_boolean_ty(),
                "unit" => self.arena.types().get_unit_ty(),
                _ => {
                    return Err(HirError::UnknownIntrinsicType(UnknownIntrinsicTypeError {
                        name: node.name.name.to_owned(),
                        span: node.name.span,
                    }))
                }
            },
        });
        let r#type = HirIntrinsicType {
            span: node.span,
            name,
            name_span: node.name.span,
            signature,
        };
        Ok(r#type)
    }

    pub fn visit_trait_item(&'ta self, node: &'ast AstTraitItem) -> HirResult<HirTrait<'ta>> {
        let name = self.arena.names().get(&node.name.name);
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parameter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let mut members = BTreeMap::new();
        for member in node.members.iter() {
            let signature = self.visit_trait_function_item(member)?;
            let name = self.arena.names().get(&member.name.name);
            members.insert(name, signature);
        }
        let signature = self.arena.intern(HirTraitApiSignature {
            span: node.span,
            type_parameters,
            name,
            name_span: node.name.span,
            methods: members,
        });
        let r#trait = HirTrait {
            span: node.span,
            name,
            name_span: node.name.span,
            signature,
        };
        Ok(r#trait)
    }

    pub fn visit_trait_function_item(
        &'ta self,
        node: &'ast AstTraitFunctionItem,
    ) -> HirResult<&'ta HirFunctionApiSignature<'ta>> {
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_type_parameter_item(p))
            .collect::<HirResult<Vec<_>>>()?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => self.arena.types().get_unit_ty(),
        };
        let return_type_annotation = node.return_type.as_ref().map(|t| *t.span());
        let signature = self.arena.intern(HirFunctionApiSignature {
            span: node.span,
            parameters,
            type_parameters,
            return_type,
            return_type_annotation,
        });
        Ok(signature)
    }

    pub fn visit_instance_item(
        &'ta self,
        node: &'ast AstInstanceItem,
    ) -> HirResult<HirInstance<'ta>> {
        let name = self.arena.names().get(&node.name.name);
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
        let signature = self.arena.intern(HirInstanceApiSignature {
            span: node.span,
            name,
            name_span: node.name.span,
            type_arguments: instantiation_type_parameters.clone(),
            trait_name: name,
            trait_name_span: node.name.span,
            methods: members.iter().map(|m| (m.name, m.signature)).collect(),
        });
        let instance = HirInstance {
            span: node.span,
            name,
            name_span: node.name.span,
            instantiation_type_parameters,
            members,
            signature,
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
    pub fn visit_type_item(&'ta self, node: &'ast AstStructItem) -> HirResult<HirStruct<'ta>> {
        let name = self.arena.names().get(&node.name.name);
        let mut fields = BTreeMap::new();
        for member in node.members.iter() {
            let ty = self.visit_type(&member.ty)?;
            let field = self.arena.intern(HirStructFieldApiSignature {
                span: member.span,
                name: self.arena.names().get(&member.name.name),
                name_span: member.name.span,
                ty,
                ty_annotation: *member.ty.span(),
            });
            let field_name = self.arena.names().get(&member.name.name);
            fields.insert(field_name, &*field);
        }
        let signature = self.arena.intern(HirStructApiSignature {
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

    pub fn visit_stmt(&'ta self, node: &'ast AstStmt) -> HirResult<HirStmt<'ta>> {
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

    pub fn visit_let_stmt(&'ta self, node: &'ast AstLetStmt) -> HirResult<HirStmt<'ta>> {
        let name = self.arena.names().get(&node.name.name);
        let ty = match &node.ty {
            Some(t) => self.visit_type(t)?,
            None => self.arena.types().get_uninitialized_ty(),
        };
        let value = self.visit_expr(&node.value)?;
        let hir = HirStmt::Let(HirLetStmt {
            span: node.span,
            name,
            name_span: node.name.span,
            ty,
            type_annotation: node.ty.as_ref().map(|t| *t.span()),
            value,
        });
        Ok(hir)
    }

    pub fn visit_return_stmt(&'ta self, node: &'ast AstReturnStmt) -> HirResult<HirStmt<'ta>> {
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
    pub fn visit_for_stmt(&'ta self, node: &'ast AstForStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth.borrow_mut().push_back(node);
        // Build the let statement for the initializer
        let initializer = node
            .initializer
            .as_ref()
            .map(|i| -> HirResult<HirLetStmt> {
                Ok(HirLetStmt {
                    span: i.span,
                    name: self.arena.names().get(&i.name.name),
                    name_span: i.name.span,
                    ty: self.arena.types().get_uninitialized_ty(),
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
                    ty: self.arena.types().get_uninitialized_ty(),
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
        self.loop_depth.borrow_mut().pop_back();
        Ok(hir)
    }

    /// Translate an if statement into a conditional expression.
    ///
    /// The synthesis of the if statement simply replaces a missing unhappy path with an empty
    /// block.
    pub fn visit_if_stmt(&'ta self, node: &'ast AstIfStmt) -> HirResult<HirStmt<'ta>> {
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

    pub fn visit_break_stmt(&'ta self, node: &'ast AstBreakStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .borrow()
            .back()
            .ok_or(HirError::BreakOutsideLoop(BreakOutsideLoopError {
                span: node.span,
            }))?;
        let hir = HirStmt::Break(HirBreakStmt { span: node.span });
        Ok(hir)
    }

    pub fn visit_expr_stmt(&'ta self, node: &'ast AstExprStmt) -> HirResult<HirStmt<'ta>> {
        let expr = self.visit_expr(&node.expr)?;
        let hir = HirStmt::Expr(HirExprStmt {
            span: node.span,
            expr,
        });
        Ok(hir)
    }

    pub fn visit_continue_stmt(&'ta self, node: &'ast AstContinueStmt) -> HirResult<HirStmt<'ta>> {
        self.loop_depth
            .borrow()
            .back()
            .ok_or(HirError::ContinueOutsideLoop(ContinueOutsideLoopError {
                span: node.span,
            }))?;
        let hir = HirStmt::Continue(HirContinueStmt { span: node.span });
        Ok(hir)
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
    pub fn visit_type(&'ta self, node: &'ast AstType) -> HirResult<&'ta HirTy<'ta>> {
        let ty = match node {
            AstType::Unit(_) => self.arena.types().get_unit_ty(),
            AstType::Integer32(_) => self.arena.types().get_integer32_ty(),
            AstType::Boolean(_) => self.arena.types().get_boolean_ty(),
            AstType::Named(t) => self
                .arena
                .types()
                .get_nominal_ty(self.arena.names().get(&t.name.name), t.name.span),
            AstType::Pointer(t) => self.arena.types().get_pointer_ty(self.visit_type(t.inner)?),
        };
        Ok(ty)
    }
}
