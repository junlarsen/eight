use crate::instruction::MirInstructionId;
use function::MirFunction;
use std::ops::Deref;

pub mod arena;
pub mod builder;
pub mod error;
mod function;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod ty;
pub mod value;

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    pub functions: Vec<MirFunction<'mir>>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
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
