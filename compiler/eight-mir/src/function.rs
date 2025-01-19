use crate::instruction::{MirInstruction, MirInstructionId};
use crate::ty::MirFunctionType;
use crate::value::{MirValue, MirValueId};
use crate::{MirBasicBlock, MirBasicBlockId};
use std::collections::BTreeMap;

#[derive(Debug, Default)]
pub struct MirFunctionData<'mir> {
    pub blocks: BTreeMap<MirBasicBlockId, MirBasicBlock<'mir>>,
    pub values: BTreeMap<MirValueId, MirValue<'mir>>,
    pub instructions: BTreeMap<MirInstructionId, MirInstruction<'mir>>,
}

impl<'mir> MirFunctionData<'mir> {
    pub fn instructions(&self) -> impl Iterator<Item = &MirInstruction<'mir>> {
        self.instructions.values()
    }

    /// Get the instruction with the given id.
    pub fn get_instruction(&self, id: MirInstructionId) -> Option<&MirInstruction<'mir>> {
        self.instructions.get(&id)
    }

    pub fn blocks(&self) -> impl Iterator<Item = &MirBasicBlock<'mir>> {
        self.blocks.values()
    }

    /// Get the basic block with the given id.
    pub fn get_basic_block(&self, id: MirBasicBlockId) -> Option<&MirBasicBlock<'mir>> {
        self.blocks.get(&id)
    }

    pub fn values(&self) -> impl Iterator<Item = &MirValue<'mir>> {
        self.values.values()
    }

    /// Get the value with the given id.
    pub fn get_value(&self, id: MirValueId) -> Option<&MirValue<'mir>> {
        self.values.get(&id)
    }
}

#[derive(Debug)]
pub struct MirFunction<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirFunctionType<'mir>,
    pub data: MirFunctionData<'mir>,
}

impl<'mir> MirFunction<'mir> {
    /// Is the function expected to be resolved at link time?
    ///
    /// Functions with empty bodies are considered external.
    pub fn is_external(&self) -> bool {
        self.data.blocks.is_empty()
    }

    pub fn data(&self) -> &MirFunctionData<'mir> {
        &self.data
    }
}
