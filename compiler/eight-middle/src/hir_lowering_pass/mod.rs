use crate::context::CompileContext;
use crate::hir::HirModule;
use crate::hir::HirTy;
use crate::hir::{
    HirBinaryOpExpr, HirBooleanLiteralExpr, HirCallExpr, HirExpr, HirIntegerLiteralExpr,
    HirReferenceExpr, HirUnaryOpExpr,
};
use crate::hir::{HirExprStmt, HirFunction, HirLetStmt, HirStmt};
use crate::intrinsic::IntrinsicCandidate;
use crate::mir::MirModule;
use crate::mir::MirType;
use crate::mir::MirValueId;
use crate::mir_builder::{MirFunctionBuilder, MirModuleContext};
use crate::mir_error::MirResult;
use crate::scope::Scope;
use crate::LinkageType;
use eight_diagnostics::{ice, sanity_check};

pub struct MirModuleLoweringPass<'mir> {
    cc: &'mir CompileContext<'mir>,
    /// Mapping between local names and their MIR value ids.
    locals: Scope<&'mir str, MirValueId>,
}

impl<'mir> MirModuleLoweringPass<'mir> {
    pub fn new(cc: &'mir CompileContext<'mir>) -> Self {
        Self {
            cc,
            locals: Scope::default(),
        }
    }
}

impl<'hir, 'mir> MirModuleLoweringPass<'mir> {
    pub fn visit_module(&mut self, module: &'hir HirModule<'hir>) -> MirResult<MirModule<'mir>> {
        let mut module_builder = MirModuleContext::new(self.cc, module);
        // Forward declare all functions contained in the module
        for function in module.body.functions.values() {
            let return_type = self.visit_ty(function.signature.return_type)?;
            let parameters = function
                .signature
                .parameters
                .iter()
                .map(|p| self.visit_ty(p.ty))
                .collect::<MirResult<Vec<_>>>()?;
            let MirType::Function(ty) = self.cc.mir_function_type(return_type, parameters) else {
                ice!("didnt get function type from arena");
            };
            let name = self.cc.intern_str(function.name);
            module_builder.forward_declare_function(name, ty);
        }
        // Generate the MIR code for all functions
        for function in module.body.functions.values() {
            let name = self.cc.intern_str(function.name);
            let Some(id) = module_builder.data().get_function_id(name) else {
                ice!(format!("failed to find function id for {}", function.name));
            };
            let Some(ty) = module_builder.data().get_function_type(id) else {
                ice!(format!(
                    "failed to find function type for {}",
                    function.name
                ));
            };
            let mut builder = MirFunctionBuilder::new(self.cc, name, ty, id);
            self.visit_function(function, &mut builder, &module_builder)?;
            module_builder.implement_function(id, builder.build());
        }
        Ok(module_builder.build())
    }

    pub fn visit_function(
        &mut self,
        node: &'hir HirFunction<'hir>,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
    ) -> MirResult<()> {
        assert!(
            !node.signature.is_generic(),
            "cannot lower generic functions at this time"
        );
        // If the function is external, it doesn't get any code, and the code generator will assume
        // that it must be externally defined and resolved at link time.
        if node.linkage_type == LinkageType::External {
            return Ok(());
        }
        self.locals.enter_scope();

        let entry = b.build_basic_block(Some("entry"));
        b.move_insertion_point(entry);
        for parameter in node.signature.parameters.iter() {
            let ty = self.visit_ty(parameter.ty)?;
            let name = self.cc.intern_str(parameter.name);
            let argument = b.build_argument(name, ty);
            self.locals.add(name, argument);
        }
        for stmt in node.body.iter() {
            self.visit_stmt(b, cx, stmt)?;
        }
        self.locals.leave_scope();
        Ok(())
    }

    /// Translate a statement into MIR.
    pub fn visit_stmt(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        stmt: &'hir HirStmt<'hir>,
    ) -> MirResult<()> {
        match stmt {
            HirStmt::Let(s) => self.visit_let_stmt(b, cx, s),
            HirStmt::Expr(s) => self.visit_expr_stmt(b, cx, s),
            HirStmt::Loop(_)
            | HirStmt::Return(_)
            | HirStmt::If(_)
            | HirStmt::Block(_)
            | HirStmt::Break(_)
            | HirStmt::Continue(_) => unimplemented!("cannot lower this statement"),
        }
    }

    /// Translate a let statement into MIR.
    ///
    /// A let statement requires a local stack allocation, and a store of the initializer value into
    /// said local.
    ///
    /// ```text
    /// let x = 1;
    /// ```
    ///
    /// Assuming the constant integer 1 is translated available in %1, the above MIR would look like
    /// this:
    ///
    /// ```text
    /// bb0:
    ///   %1 = ...
    ///   %2 = mem.alloca i32
    ///   store %1, %2
    /// ```
    pub fn visit_let_stmt(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        stmt: &'hir HirLetStmt<'hir>,
    ) -> MirResult<()> {
        let value = self.visit_expr(b, cx, &stmt.value)?;
        let value_ty = b.data().get_value_type(value);
        let ptr = b.build_alloca(cx, value_ty, None);
        b.build_store(cx, value, ptr, None);
        let name = self.cc.intern_str(stmt.name);
        self.locals.add(name, ptr);
        Ok(())
    }

    pub fn visit_expr_stmt(
        &mut self,
        builder: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        stmt: &'hir HirExprStmt<'hir>,
    ) -> MirResult<()> {
        let _ = self.visit_expr(builder, cx, &stmt.expr)?;
        Ok(())
    }

    /// Translate an expression into MIR.
    pub fn visit_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirExpr<'hir>,
    ) -> MirResult<MirValueId> {
        match expr {
            HirExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(b, cx, e),
            HirExpr::Reference(e) => self.visit_reference_expr(b, cx, e),
            HirExpr::Call(e) => self.visit_call_expr(b, cx, e),
            HirExpr::BooleanLiteral(e) => self.visit_boolean_literal_expr(b, cx, e),
            HirExpr::BinaryOp(e) => self.visit_binary_op_expr(b, cx, e),
            HirExpr::UnaryOp(e) => self.visit_unary_op_expr(b, cx, e),
            HirExpr::Group(_)
            | HirExpr::AddressOf(_)
            | HirExpr::Deref(_)
            | HirExpr::ConstantIndex(_)
            | HirExpr::CallableReference(_)
            | HirExpr::OffsetIndex(_)
            | HirExpr::Construct(_)
            | HirExpr::Assign(_) => unimplemented!("cannot lower this expression"),
        }
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        _: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirIntegerLiteralExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let inst = b.build_constant_integer32(expr.value, self.cc.mir_i32_type());
        Ok(inst)
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        _: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirBooleanLiteralExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let inst = b.build_constant_bool(expr.value, self.cc.mir_bool_type());
        Ok(inst)
    }

    pub fn visit_reference_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirReferenceExpr<'hir>,
    ) -> MirResult<MirValueId> {
        // We need to see if this is the name of a function, and if so, we need to lower it to a
        // function value.
        if expr.is_reference_to_function {
            let name = self.cc.intern_str(expr.name);
            let id = cx.data().get_function_id(name).unwrap_or_else(|| {
                ice!(format!(
                    "failed to find function id for {} despite passing type checker",
                    expr.name
                ));
            });
            return Ok(b.build_function_ref(id));
        };
        // Arguments can be used directly, but locals need to be loaded.
        let id = self.locals.find(&expr.name).unwrap_or_else(|| {
            ice!(format!("failed to find local value for {}", expr.name));
        });
        let value_ty = b.data().get_value_type(*id);
        let expected_ty = self.visit_ty(expr.ty)?;
        // If it is a pointer type, we automatically dereference it.
        if let MirType::Pointer(_) = value_ty {
            let load = b.build_load(cx, *id, expected_ty, None);
            return Ok(load);
        }
        Ok(*id)
    }

    pub fn visit_call_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirCallExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let callee = self.visit_expr(b, cx, &expr.callee)?;
        let arguments = expr
            .arguments
            .iter()
            .map(|a| self.visit_expr(b, cx, a))
            .collect::<MirResult<Vec<_>>>()?;
        let return_ty = self.visit_ty(expr.ty)?;
        let call = b.build_call(cx, callee, arguments, return_ty, None);
        Ok(call)
    }

    /// Translate a binary operator expression into MIR.
    ///
    /// Binary operators are special, because they can be overloaded by the user by adding an
    /// instance of the trait the operator corresponds to.
    ///
    /// If the trait is not overloaded in user land, but instead defined through the compiler
    /// intrinsics in the standard library, we can lower the operator into the corresponding MIR
    /// instructions.
    ///
    /// When this is not the case, we need to construct a function call to the trait instance
    /// function that matches the expression's types.
    pub fn visit_binary_op_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirBinaryOpExpr<'hir>,
    ) -> MirResult<MirValueId> {
        if let Some(candidate) = HirBinaryOpExpr::is_implemented_as_intrinsic(expr) {
            return self.visit_binary_intrinsic_candidate(b, cx, candidate, expr);
        }
        unimplemented!("userland instance binary operator calling is not yet implemented")
    }

    /// Translate a unary operator expression into MIR.
    ///
    /// Unary operators are special, because they can be overloaded by the user by adding an
    /// instance of the trait the operator corresponds to.
    ///
    /// If the trait is not overloaded in user land, but instead defined through the compiler
    /// intrinsics in the standard library, we can lower the operator into the corresponding MIR
    /// instructions.
    ///
    /// When this is not the case, we need to construct a function call to the trait instance
    /// function that matches the expression's types.
    pub fn visit_unary_op_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirUnaryOpExpr<'hir>,
    ) -> MirResult<MirValueId> {
        if let Some(candidate) = HirUnaryOpExpr::is_implemented_as_intrinsic(expr) {
            return self.visit_unary_intrinsic_candidate(b, cx, candidate, expr);
        }
        unimplemented!("userland instance unary operator calling is not yet implemented")
    }

    /// Translate a binary operator that is guaranteed to be implemented as an intrinsic.
    ///
    /// The standard library only defines operators on equal types, so we can safely assume that
    /// both LHS and RHS are of the same type, and that the resulting type of this operator is the
    /// same as the LHS (and consequently RHS) type.
    pub fn visit_binary_intrinsic_candidate(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        candidate: IntrinsicCandidate,
        expr: &'hir HirBinaryOpExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let lhs = self.visit_expr(b, cx, &expr.lhs)?;
        let rhs = self.visit_expr(b, cx, &expr.rhs)?;
        let lhs_ty = b.data().get_value_type(lhs);
        let rhs_ty = b.data().get_value_type(rhs);
        sanity_check!(lhs_ty == rhs_ty, "lhs and rhs types must be equal");
        let inst = match candidate {
            IntrinsicCandidate::IntegerAdd => b.build_add(cx, lhs, rhs, lhs_ty, None),
            IntrinsicCandidate::IntegerSub => b.build_sub(cx, lhs, rhs, lhs_ty, None),
            IntrinsicCandidate::IntegerMul => b.build_mul(cx, lhs, rhs, lhs_ty, None),
            IntrinsicCandidate::IntegerDiv => b.build_div(cx, lhs, rhs, lhs_ty, None),
            _ => unimplemented!("binary operator {candidate:?} is not yet implemented"),
        };
        Ok(inst)
    }

    /// Translate a unary operator that is guaranteed to be implemented as an intrinsic.
    ///
    /// The standard library only defines unary operators on types that result in the same type.
    pub fn visit_unary_intrinsic_candidate(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        candidate: IntrinsicCandidate,
        expr: &'hir HirUnaryOpExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let operand = self.visit_expr(b, cx, &expr.operand)?;
        let ty = b.data().get_value_type(operand);
        let inst = match candidate {
            // Negation of a number is implemented as subtraction from zero.
            IntrinsicCandidate::IntegerNeg => {
                let zero = b.build_constant_integer32(0, self.cc.mir_i32_type());
                b.build_sub(cx, zero, operand, ty, None)
            }
            _ => unimplemented!("unary operator {candidate:?} is not yet implemented"),
        };
        Ok(inst)
    }

    /// Translate a type into MIR.
    ///
    /// The type system in MIR is substantially smaller and simpler than the language and HIR. This
    /// means we can do a lot of shortcutting here.
    pub fn visit_ty(&self, node: &'hir HirTy<'hir>) -> MirResult<&'mir MirType<'mir>> {
        match node {
            HirTy::Integer32(_) => Ok(self.cc.mir_i32_type()),
            HirTy::Boolean(_) => Ok(self.cc.mir_bool_type()),
            HirTy::Unit(_) => Ok(self.cc.mir_void_type()),
            HirTy::Pointer(_) => Ok(self.cc.mir_pointer_type()),
            HirTy::Function(_)
            | HirTy::Nominal(_)
            | HirTy::Variable(_)
            | HirTy::Meta(_)
            | HirTy::Uninitialized(_) => unimplemented!("cannot lower this type"),
        }
    }
}
