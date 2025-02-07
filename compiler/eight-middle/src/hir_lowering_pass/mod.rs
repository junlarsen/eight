use crate::context::CompileContext;
use crate::hir::{
    HirBooleanLiteralExpr, HirCallExpr, HirExpr, HirIntegerLiteralExpr, HirReferenceExpr,
};
use crate::hir::{HirExprStmt, HirFunction, HirLetStmt, HirStmt};
use crate::hir::{HirGroupExpr, HirTy};
use crate::hir::{HirModule, HirReferenceSymbol};
use crate::mir::MirModule;
use crate::mir::MirTy;
use crate::mir::MirValueId;
use crate::mir_builder::{MirFunctionBuilder, MirModuleContext};
use crate::scope::Scope;
use crate::LinkageType;
use crate::MirResult;
use eight_diagnostics::ice;

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
            let MirTy::Function(ty) = self.cc.mir_function_type(return_type, parameters) else {
                ice!("didnt get function type from arena");
            };
            let name = self.cc.intern_str(function.name);
            module_builder.forward_declare_function(name, ty);
        }
        // Generate the MIR code for all functions
        for function in module.body.functions.values() {
            let name = self.cc.intern_str(function.name);
            let Some(id) = module_builder.data().get_function_id(name) else {
                ice!("failed to find function id for {}", function.name);
            };
            let Some(ty) = module_builder.data().get_function_type(id) else {
                ice!("failed to find function type for {}", function.name);
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
        // If the function is external, it doesn't get any code, and the code generator will assume
        // that it must be externally defined and resolved at link time.
        if node.linkage_type == LinkageType::External {
            return Ok(());
        }
        assert!(
            !node.signature.is_generic(),
            "cannot lower generic functions at this time"
        );
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
            HirExpr::Group(e) => self.visit_group_expr(b, cx, e),
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
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirReferenceExpr<'hir>,
    ) -> MirResult<MirValueId> {
        match &expr.kind {
            HirReferenceSymbol::Local(local) => {
                let id = self.locals.find(&local.name).unwrap_or_else(|| {
                    ice!("failed to find local value for {}", local.name);
                });
                let value_ty = b.data().get_value_type(*id);
                let expected_ty = self.visit_ty(expr.ty)?;
                // If it is a pointer type, we automatically dereference it.
                if let MirTy::Pointer(_) = value_ty {
                    let load = b.build_load(cx, *id, expected_ty, None);
                    return Ok(load);
                }
                Ok(*id)
            }
            HirReferenceSymbol::Function(symbol) => {
                // TODO: Mangle the name along with the type arguments.
                let name = self.cc.intern_str(symbol.name);
                let id = cx.data().get_function_id(name).unwrap_or_else(|| {
                    ice!(
                        "failed to find function id for {} despite passing type checker",
                        name
                    );
                });
                Ok(b.build_function_ref(id))
            }
            HirReferenceSymbol::Intrinsic(_) => unimplemented!(),
            HirReferenceSymbol::TraitMethod(_) => unimplemented!(),
        }
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

    pub fn visit_group_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirGroupExpr<'hir>,
    ) -> MirResult<MirValueId> {
        self.visit_expr(b, cx, &expr.inner)
    }

    /// Translate a type into MIR.
    ///
    /// The type system in MIR is substantially smaller and simpler than the language and HIR. This
    /// means we can do a lot of shortcutting here.
    pub fn visit_ty(&self, node: &'hir HirTy<'hir>) -> MirResult<&'mir MirTy<'mir>> {
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
