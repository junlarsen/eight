use crate::instruction::{MirInstruction, MirInstructionId};
use crate::ty::MirFunctionType;
use crate::value::{MirValue, MirValueId};
use std::collections::BTreeMap;

pub mod arena;
pub mod builder;
pub mod error;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod ty;
pub mod value;

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    pub functions: BTreeMap<&'mir str, MirFunction<'mir>>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
pub struct MirFunction<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirFunctionType<'mir>,
    /// List of basic blocks built for the function.
    blocks: BTreeMap<MirBasicBlockId, MirBasicBlock<'mir>>,
    /// List of values built for the function.
    values: BTreeMap<MirValueId, MirValue<'mir>>,
    /// List of instructions built for the function.
    instructions: BTreeMap<MirInstructionId, MirInstruction<'mir>>,
}

impl<'mir> MirFunction<'mir> {
    /// Is the function expected to be resolved at link time?
    ///
    /// Functions with empty bodies are considered external.
    pub fn is_external(&self) -> bool {
        self.blocks.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirBasicBlockId(pub usize);

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
