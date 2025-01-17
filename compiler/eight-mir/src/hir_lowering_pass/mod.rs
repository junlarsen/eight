use crate::arena::MirArena;

pub struct MirModuleLoweringPass<'mir> {
    arena: &'mir MirArena<'mir>,
}

impl<'mir> MirModuleLoweringPass<'mir> {
    pub fn new(arena: &'mir MirArena<'mir>) -> Self {
        Self { arena }
    }
}

impl<'mir> MirModuleLoweringPass<'mir> {}
