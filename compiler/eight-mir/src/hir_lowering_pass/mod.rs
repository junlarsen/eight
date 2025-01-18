use crate::arena::MirArena;
use crate::error::MirResult;
use crate::MirModule;
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
        let mir = MirModule::new();
        Ok(mir)
    }
}
