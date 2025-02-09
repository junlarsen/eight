use crate::builtin::CompilerIntrinsic;
use crate::context::CompileSession;
use crate::hir::HirTy;
use crate::hir::{
    HirBooleanLiteralExpr, HirCallExpr, HirExpr, HirIntegerLiteralExpr, HirReferenceExpr,
};
use crate::hir::{HirExprStmt, HirFunction, HirLetStmt, HirStmt};
use crate::hir::{HirModule, HirReferenceSymbol};
use crate::mir::function::{MirFunction, MirFunctionBuilder};
use crate::mir::module::MirModuleContext;
use crate::mir::module::{MirModule, MirModuleInterface};
use crate::mir::MirValueRef;
use crate::mir::{MirFunctionRef, MirFunctionType, MirTy};
use crate::scope::Scope;
use crate::LinkageType;
use crate::MirResult;
use eight_diagnostics::ice;

pub struct HirModuleLoweringPass<'mir> {
    session: &'mir CompileSession<'mir>,
    /// Mapping between local names and their MIR value ids.
    locals: Scope<&'mir str, MirValueRef>,
}

impl<'mir> HirModuleLoweringPass<'mir> {
    pub fn new(session: &'mir CompileSession<'mir>) -> Self {
        Self {
            session,
            locals: Scope::default(),
        }
    }
}

impl<'hir, 'mir> HirModuleLoweringPass<'mir> {
    pub fn visit_module(&mut self, module: &'hir HirModule<'hir>) -> MirResult<MirModule<'mir>> {
        // Extract all items into the module interface
        let mut interface = MirModuleInterface::default();
        for (name, signature) in module.signature.query_functions() {
            let return_type = self.visit_ty(signature.return_type)?;
            let parameters = signature
                .parameters
                .iter()
                .map(|p| self.visit_ty(p.ty))
                .collect::<MirResult<Vec<_>>>()?;
            let MirTy::Function(ty) = self.session.mir_function_type(return_type, parameters)
            else {
                ice!("didnt get function type from arena");
            };
            let name = self.session.intern_str(name);
            interface.insert_function(name, ty);
        }

        let mut module_builder = MirModuleContext::new(self.session);
        // Generate the MIR code for all functions
        for function in module.body.functions.values() {
            let name = self.session.intern_str(function.name);
            let Some(ty) = interface.get_function(name) else {
                ice!("failed to find function type for {}", function.name);
            };
            let mir_function = self.visit_function(function, name, ty, &module_builder)?;
            module_builder.insert_function(name, mir_function);
        }
        Ok(module_builder.build(interface))
    }

    pub fn visit_function(
        &mut self,
        node: &'hir HirFunction<'hir>,
        name: MirFunctionRef<'mir>,
        ty: &'mir MirFunctionType<'mir>,
        cx: &MirModuleContext<'mir>,
    ) -> MirResult<MirFunction<'mir>> {
        assert!(
            !(node.signature.is_generic() && matches!(node.linkage_type, LinkageType::Eight)),
            "cannot lower generic functions at this time"
        );
        self.locals.enter_scope();
        let mut function_builder = MirFunctionBuilder::new(self.session, name, ty);
        // If the function is external, it doesn't get any code, and the code generator will assume
        // that it must be externally defined and resolved at link time.
        if node.linkage_type == LinkageType::External {
            return Ok(function_builder.build());
        }

        let entry = function_builder.build_basic_block(Some("entry"));
        function_builder.move_insertion_point(entry);
        for parameter in node.signature.parameters.iter() {
            let ty = self.visit_ty(parameter.ty)?;
            let name = self.session.intern_str(parameter.name);
            let argument = function_builder.build_argument(name, ty);
            self.locals.add(name, argument);
        }
        for stmt in node.body.iter() {
            self.visit_stmt(&mut function_builder, cx, stmt)?;
        }
        self.locals.leave_scope();
        Ok(function_builder.build())
    }

    /// Translate a statement into MIR.
    pub fn visit_stmt(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
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
        cx: &MirModuleContext<'mir>,
        stmt: &'hir HirLetStmt<'hir>,
    ) -> MirResult<()> {
        let value = self.visit_expr(b, cx, &stmt.value)?;
        let value_ty = b.data().get_value_type(&value);
        let ptr = b.build_alloca(cx, value_ty, None);
        b.build_store(cx, value, ptr, None);
        let name = self.session.intern_str(stmt.name);
        self.locals.add(name, ptr);
        Ok(())
    }

    pub fn visit_expr_stmt(
        &mut self,
        builder: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
        stmt: &'hir HirExprStmt<'hir>,
    ) -> MirResult<()> {
        let _ = self.visit_expr(builder, cx, &stmt.expr)?;
        Ok(())
    }

    /// Translate an expression into MIR.
    pub fn visit_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
        expr: &'hir HirExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        match expr {
            HirExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(b, cx, e),
            HirExpr::Reference(e) => self.visit_reference_expr(b, cx, e),
            HirExpr::Call(e) => self.visit_call_expr(b, cx, e),
            HirExpr::BooleanLiteral(e) => self.visit_boolean_literal_expr(b, cx, e),
            HirExpr::AddressOf(_)
            | HirExpr::Deref(_)
            | HirExpr::ConstantIndex(_)
            | HirExpr::OffsetIndex(_)
            | HirExpr::Construct(_)
            | HirExpr::Assign(_) => unimplemented!("cannot lower this expression"),
        }
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        _: &MirModuleContext<'mir>,
        expr: &'hir HirIntegerLiteralExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        let inst = b.build_constant_integer32(expr.value, self.session.mir_i32_type());
        Ok(inst)
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        _: &MirModuleContext<'mir>,
        expr: &'hir HirBooleanLiteralExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        let inst = b.build_constant_bool(expr.value, self.session.mir_bool_type());
        Ok(inst)
    }

    /// Translate a reference expression into MIR.
    ///
    /// At this stage in the translation pipeline, we are ensured that a [`MirReferenceExpr`] is
    /// only used to point to local variables. This means that we can safely lower it to load.
    ///
    /// Function references are lowered into [`HirCallableReferenceExpr`] nodes, which are handled
    /// by a separate visitor.
    pub fn visit_reference_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
        expr: &'hir HirReferenceExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        match &expr.kind {
            HirReferenceSymbol::Local(local) => {
                let value = self.locals.find(&local.name).unwrap_or_else(|| {
                    ice!("failed to find local value for {}", local.name);
                });
                let value_ty = b.data().get_value_type(value);
                let expected_ty = self.visit_ty(expr.ty)?;
                // If it is a pointer type, we automatically dereference it.
                if let MirTy::Pointer(_) = value_ty {
                    let load = b.build_load(cx, *value, expected_ty, None);
                    return Ok(load);
                }
                Ok(*value)
            }
            HirReferenceSymbol::Function(symbol) => {
                // TODO: Mangle the name along with the type arguments.
                let name = self.session.intern_str(symbol.name);
                Ok(b.build_function_ref(name))
            }
            HirReferenceSymbol::Intrinsic(_) => {
                ice!("called visit_reference_expr() on an intrinsic")
            }
            HirReferenceSymbol::TraitMethod(e) => {
                unimplemented!("{:?}", e)
            }
        }
    }

    pub fn visit_call_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
        expr: &'hir HirCallExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        // If the call is implemented as an intrinsic, we can lower it to a more efficient form, so
        // we delegate to intrinsic lowering instead.
        if expr.is_intrinsic() {
            return self.visit_intrinsic_call_expr(b, cx, expr);
        }
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

    pub fn visit_intrinsic_call_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir>,
        expr: &'hir HirCallExpr<'hir>,
    ) -> MirResult<MirValueRef> {
        let HirExpr::Reference(reference) = expr.callee.as_ref() else {
            ice!("visit_intrinsic_call_expr called with non-reference callee");
        };
        let HirReferenceSymbol::Intrinsic(intrinsic) = &reference.kind else {
            ice!("visit_intrinsic_call_expr called with non-intrinsic callee");
        };
        let arguments = expr
            .arguments
            .iter()
            .map(|a| self.visit_expr(b, cx, a))
            .collect::<MirResult<Vec<_>>>()?;
        let ty = self.visit_ty(expr.ty)?;
        let value = match intrinsic {
            CompilerIntrinsic::IntegerAdd => b.build_add(cx, arguments[0], arguments[1], ty, None),
            CompilerIntrinsic::IntegerSub => b.build_sub(cx, arguments[0], arguments[1], ty, None),
            CompilerIntrinsic::IntegerMul => b.build_mul(cx, arguments[0], arguments[1], ty, None),
            CompilerIntrinsic::IntegerDiv => b.build_div(cx, arguments[0], arguments[1], ty, None),

            CompilerIntrinsic::IntegerNeg => b.build_neg(cx, arguments[0], ty, None),
            _ => unimplemented!(),
        };
        Ok(value)
    }

    /// Translate a type into MIR.
    ///
    /// The type system in MIR is substantially smaller and simpler than the language and HIR. This
    /// means we can do a lot of shortcutting here.
    pub fn visit_ty(&self, node: &'hir HirTy<'hir>) -> MirResult<&'mir MirTy<'mir>> {
        match node {
            HirTy::Integer32(_) => Ok(self.session.mir_i32_type()),
            HirTy::Boolean(_) => Ok(self.session.mir_bool_type()),
            HirTy::Unit(_) => Ok(self.session.mir_void_type()),
            HirTy::Pointer(_) => Ok(self.session.mir_pointer_type()),
            HirTy::Function(_)
            | HirTy::Nominal(_)
            | HirTy::Variable(_)
            | HirTy::Meta(_)
            | HirTy::Uninitialized(_) => unimplemented!("cannot lower this type"),
        }
    }
}
