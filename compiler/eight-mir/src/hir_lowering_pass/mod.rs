use crate::arena::MirArena;
use crate::builder::MirFunctionBuilder;
use crate::error::MirResult;
use crate::ty::MirType;
use crate::{MirFunction, MirModule};
use eight_diagnostics::ice;
use eight_hir::item::HirFunction;
use eight_hir::ty::HirTy;
use eight_hir::HirModule;

pub struct MirModuleLoweringPass<'mir> {
    arena: &'mir MirArena<'mir>,
}

impl<'mir> MirModuleLoweringPass<'mir> {
    pub fn new(arena: &'mir MirArena<'mir>) -> Self {
        Self { arena }
    }
}

impl<'hir, 'mir> MirModuleLoweringPass<'mir> {
    pub fn visit_module(&self, module: &'hir HirModule<'hir>) -> MirResult<MirModule<'mir>> {
        let mut mir = MirModule::new();
        for function in module.body.functions.values() {
            let mir_function = self.visit_function(function)?;
            let name = self.arena.names().get(function.name);
            mir.functions.insert(name, mir_function);
        }
        Ok(mir)
    }

    pub fn visit_function(&self, node: &'hir HirFunction<'hir>) -> MirResult<MirFunction<'mir>> {
        assert!(
            !node.signature.is_generic(),
            "cannot lower generic functions at this time"
        );
        let parameters = node
            .signature
            .parameters
            .iter()
            .map(|p| self.visit_ty(p.ty))
            .collect::<MirResult<Vec<_>>>()?;
        let MirType::Function(ty) = self
            .arena
            .types()
            .get_function_type(self.visit_ty(node.signature.return_type)?, parameters)
        else {
            ice!("didnt get function type from arena");
        };

        let name = self.arena.names().get(node.name);
        let builder = MirFunctionBuilder::new(self.arena, ty, name);
        Ok(builder.build())
    }

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
