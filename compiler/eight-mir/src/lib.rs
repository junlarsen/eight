use crate::function::MirFunction;
use crate::instruction::MirInstructionId;
use std::collections::BTreeMap;
use std::ops::Deref;

pub mod arena;
pub mod builder;
pub mod error;
pub mod function;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod ty;
pub mod value;

#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    pub functions: BTreeMap<MirFunctionId, MirFunction<'mir>>,
}

impl<'mir> MirModuleData<'mir> {
    pub fn functions(&self) -> impl Iterator<Item = &MirFunction<'mir>> {
        self.functions.values()
    }

    pub fn get_function(&self, id: MirFunctionId) -> Option<&MirFunction<'mir>> {
        self.functions.get(&id)
    }
}

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    data: MirModuleData<'mir>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirFunctionId(pub usize);

impl Deref for MirFunctionId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirBasicBlockId(pub usize);

impl Deref for MirBasicBlockId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
pub struct MirBasicBlock<'mir> {
    pub name: &'mir str,
    pub instructions: Vec<MirInstructionId>,
}

impl<'mir> MirBasicBlock<'mir> {
    pub fn insert(&mut self, instruction: MirInstructionId) {
        self.instructions.push(instruction);
    }
}
