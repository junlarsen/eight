use crate::arena::MirArena;
use crate::builder::{MirFunctionBuilder, HirModuleContext};
use crate::error::MirResult;
use crate::ty::MirType;
use crate::value::MirValueId;
use crate::MirModule;
use eight_diagnostics::ice;
use eight_hir::expr::{HirExpr, HirIntegerLiteralExpr};
use eight_hir::item::HirFunction;
use eight_hir::stmt::{HirExprStmt, HirLetStmt, HirStmt};
use eight_hir::ty::HirTy;
use eight_hir::HirModule;
use eight_middle::LinkageType;

pub struct MirModuleLoweringPass<'mir> {
    arena: &'mir MirArena<'mir>,
}

impl<'mir> MirModuleLoweringPass<'mir> {
    pub fn new(arena: &'mir MirArena<'mir>) -> Self {
        Self { arena,
        }
    }
}

impl<'hir, 'mir> MirModuleLoweringPass<'mir> {
    pub fn visit_module(&mut self, module: &'hir HirModule<'hir>) -> MirResult<MirModule<'mir>> {
        let mut module_builder = HirModuleContext::new(self.arena);
        // Forward declare all functions contained in the module
        for function in module.body.functions.values() {
            let return_type = self.visit_ty(function.signature.return_type)?;
            let parameters = function
                .signature
                .parameters
                .iter()
                .map(|p| self.visit_ty(p.ty))
                .collect::<MirResult<Vec<_>>>()?;
            let MirType::Function(ty) = self.arena.types().get_function_type(return_type, parameters) else {
                ice!("didnt get function type from arena");
            };
            let name = self.arena.names().get(function.name);
            module_builder.forward_declare_function(name, ty);
        }
        // Generate the MIR code for all functions
        let mut functions = Vec::new();
        for function in module.body.functions.values() {
            let name = self.arena.names().get(function.name);
            let Some(id) = module_builder.get_function_id(name) else {
                ice!(format!("failed to find function id for {}", function.name));
            };
            let Some(ty) = module_builder.get_function_type(id) else {
                ice!(format!("failed to find function type for {}", function.name));
            };
            let mut builder = MirFunctionBuilder::new(self.arena, name, ty, id);
            self.visit_function(function, &module_builder, &mut builder)?;
            let f = builder.build();
            functions.push((id, f))
        }
        Ok(module_builder.build())
    }

    pub fn visit_function(&self, node: &'hir HirFunction<'hir>, cx: &HirModuleContext<'mir>, b: &mut MirFunctionBuilder<'mir>) -> MirResult<()> {
        assert!(
            !node.signature.is_generic(),
            "cannot lower generic functions at this time"
        );
        // If the function is external, it doesn't get any code, and the code generator will assume
        // that it must be externally defined and resolved at link time.
        if node.linkage_type == LinkageType::External {
            return Ok(());
        }
        let entry = b.build_basic_block(Some("entry"));
        b.move_insertion_point(entry);
        for stmt in node.body.iter() {
            self.visit_stmt(b, stmt)?;
        }
        Ok(())
    }

    /// Translate a statement into MIR.
    pub fn visit_stmt(
        &self,
        builder: &mut MirFunctionBuilder<'mir>,
        stmt: &'hir HirStmt<'hir>,
    ) -> MirResult<()> {
        match stmt {
            HirStmt::Let(s) => self.visit_let_stmt(builder, s),
            HirStmt::Expr(s) => self.visit_expr_stmt(builder, s),
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
        &self,
        builder: &mut MirFunctionBuilder<'mir>,
        stmt: &'hir HirLetStmt<'hir>,
    ) -> MirResult<()> {
        let value = self.visit_expr(builder, &stmt.value)?;
        let ptr = builder.build_alloca(self.arena.types().get_i32_type(), None);
        let store = builder.build_store(value, ptr, None);
        Ok(())
    }

    pub fn visit_expr_stmt(
        &self,
        builder: &mut MirFunctionBuilder<'mir>,
        stmt: &'hir HirExprStmt<'hir>,
    ) -> MirResult<()> {
        todo!()
    }

    /// Translate an expression into MIR.
    pub fn visit_expr(
        &self,
        builder: &mut MirFunctionBuilder<'mir>,
        expr: &'hir HirExpr<'hir>,
    ) -> MirResult<MirValueId> {
        match expr {
            HirExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(builder, e),
            HirExpr::BooleanLiteral(_)
            | HirExpr::Reference(_)
            | HirExpr::Group(_)
            | HirExpr::AddressOf(_)
            | HirExpr::Deref(_)
            | HirExpr::UnaryOp(_)
            | HirExpr::BinaryOp(_)
            | HirExpr::ConstantIndex(_)
            | HirExpr::OffsetIndex(_)
            | HirExpr::Call(_)
            | HirExpr::Construct(_)
            | HirExpr::Assign(_) => unimplemented!("cannot lower this expression"),
        }
    }

    pub fn visit_integer_literal_expr(
        &self,
        builder: &mut MirFunctionBuilder<'mir>,
        expr: &'hir HirIntegerLiteralExpr<'hir>,
    ) -> MirResult<MirValueId> {
        let inst =
            builder.build_constant_integer(expr.value as i64, self.arena.types().get_i32_type());
        Ok(inst)
    }

    /// Translate a type into MIR.
    ///
    /// The type system in MIR is substantially smaller and simpler than the language and HIR. This
    /// means we can do a lot of shortcutting here.
    pub fn visit_ty(&self, node: &'hir HirTy<'hir>) -> MirResult<&'mir MirType<'mir>> {
        match node {
            HirTy::Integer32(_) => Ok(self.arena.types().get_i32_type()),
            HirTy::Boolean(_) => Ok(self.arena.types().get_bool_type()),
            HirTy::Unit(_) => Ok(self.arena.types().get_void_type()),
            HirTy::Pointer(_) => Ok(self.arena.types().get_pointer_type()),
            HirTy::Function(_)
            | HirTy::Nominal(_)
            | HirTy::Variable(_)
            | HirTy::Meta(_)
            | HirTy::Uninitialized(_) => unimplemented!("cannot lower this type"),
        }
    }
}
