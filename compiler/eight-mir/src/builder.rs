use crate::arena::MirArena;
use crate::ty::MirFunctionType;
use crate::value::{MirArgument, MirValue, MirValueKind};
use crate::{MirBlock, MirFunction};
use std::collections::BTreeMap;

/// A builder for MIR functions.
///
/// A MIR builder is responsible for building a complete MIR function.
pub struct MirFunctionBuilder<'mir> {
    ty: &'mir MirFunctionType<'mir>,
    name: &'mir str,
    local_count: u32,
    locals: BTreeMap<&'mir str, MirValue<'mir>>,
    blocks: Vec<MirBlock<'mir>>,
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Create a new MIR function builder based on a signature.
    pub fn new(
        arena: &'mir MirArena<'mir>,
        ty: &'mir MirFunctionType<'mir>,
        name: &'mir str,
    ) -> Self {
        let mut locals = BTreeMap::new();
        for (index, ty) in ty.parameters.iter().enumerate() {
            let name = arena.names().get_usize(index);
            let arg = MirArgument { name, ty };
            let val = MirValue {
                ty,
                val: MirValueKind::Argument(arg),
            };
            locals.insert(name, val);
        }

        Self {
            ty,
            name,
            local_count: locals.len() as u32,
            locals,
            blocks: Vec::new(),
        }
    }

    /// Complete the function and consume the builder.
    pub fn build(self) -> MirFunction<'mir> {
        MirFunction {
            ty: self.ty,
            name: self.name,
            basic_blocks: self.blocks,
        }
    }
}
