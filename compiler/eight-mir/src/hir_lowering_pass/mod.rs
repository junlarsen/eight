use crate::arena::MirArena;
use crate::builder::{MirFunctionBuilder, MirModuleContext};
use crate::error::MirResult;
use crate::module::MirModule;
use crate::ty::MirType;
use crate::value::MirValueId;
use eight_diagnostics::ice;
use eight_middle::hir::expr::{
    HirBooleanLiteralExpr, HirCallExpr, HirExpr, HirIntegerLiteralExpr, HirReferenceExpr,
};
use eight_middle::hir::item::HirFunction;
use eight_middle::hir::stmt::{HirExprStmt, HirLetStmt, HirStmt};
use eight_middle::hir::ty::HirTy;
use eight_middle::context::LocalContext;
use eight_middle::hir::module::HirModule;
use eight_middle::LinkageType;

pub struct MirModuleLoweringPass<'mir> {
    arena: &'mir MirArena<'mir>,
    /// Mapping between local names and their MIR value ids.
    locals: LocalContext<&'mir str, MirValueId>,
}

impl<'mir> MirModuleLoweringPass<'mir> {
    pub fn new(arena: &'mir MirArena<'mir>) -> Self {
        Self {
            arena,
            locals: LocalContext::default(),
        }
    }
}

impl<'hir, 'mir> MirModuleLoweringPass<'mir> {
    pub fn visit_module(&mut self, module: &'hir HirModule<'hir>) -> MirResult<MirModule<'mir>> {
        let mut module_builder = MirModuleContext::new(self.arena, module);
        // Forward declare all functions contained in the module
        for function in module.body.functions.values() {
            let return_type = self.visit_ty(function.signature.return_type)?;
            let parameters = function
                .signature
                .parameters
                .iter()
                .map(|p| self.visit_ty(p.ty))
                .collect::<MirResult<Vec<_>>>()?;
            let MirType::Function(ty) = self
                .arena
                .types()
                .get_function_type(return_type, parameters)
            else {
                ice!("didnt get function type from arena");
            };
            let name = self.arena.names().get(function.name);
            module_builder.forward_declare_function(name, ty);
        }
        // Generate the MIR code for all functions
        for function in module.body.functions.values() {
            let name = self.arena.names().get(function.name);
            let Some(id) = module_builder.data().get_function_id(name) else {
                ice!(format!("failed to find function id for {}", function.name));
            };
            let Some(ty) = module_builder.data().get_function_type(id) else {
                ice!(format!(
                    "failed to find function type for {}",
                    function.name
                ));
            };
            let mut builder = MirFunctionBuilder::new(self.arena, name, ty, id);
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
            let name = self.arena.names().get(parameter.name);
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
        let name = self.arena.names().get(stmt.name);
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
            HirExpr::Group(_)
            | HirExpr::AddressOf(_)
            | HirExpr::Deref(_)
            | HirExpr::UnaryOp(_)
            | HirExpr::BinaryOp(_)
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
        let inst = b.build_constant_integer32(expr.value, self.arena.types().get_i32_type());
        Ok(inst)
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        b: &mut MirFunctionBuilder<'mir>,
        _: &MirModuleContext<'mir, 'hir>,
        expr: &'hir HirBooleanLiteralExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let inst = b.build_constant_bool(expr.value, self.arena.types().get_bool_type());
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
            let name = self.arena.names().get(expr.name);
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
        // If it is a pointer type, we automatically dereference it.
        if let MirType::Pointer(v) = value_ty {
            let load = b.build_load(cx, *id, v.inner, None);
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

    /// Translate a type into MIR.
    ///
    /// The type system in MIR is substantially smaller and simpler than the language and HIR. This
    /// means we can do a lot of shortcutting here.
    pub fn visit_ty(&mut self, node: &'hir HirTy<'hir>) -> MirResult<&'mir MirType<'mir>> {
        match node {
            HirTy::Integer32(_) => Ok(self.arena.types().get_i32_type()),
            HirTy::Boolean(_) => Ok(self.arena.types().get_bool_type()),
            HirTy::Unit(_) => Ok(self.arena.types().get_void_type()),
            HirTy::Pointer(i) => Ok(self.arena.types().get_pointer_type(self.visit_ty(i.inner)?)),
            HirTy::Function(_)
            | HirTy::Nominal(_)
            | HirTy::Variable(_)
            | HirTy::Meta(_)
            | HirTy::Uninitialized(_) => unimplemented!("cannot lower this type"),
        }
    }
}
