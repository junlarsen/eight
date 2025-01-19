use crate::instruction::{MirInstruction, MirInstructionId};
use crate::ty::{MirFunctionType, MirType};
use crate::value::{MirValue, MirValueId};
use crate::{MirBasicBlock, MirBasicBlockId};
use eight_diagnostics::ice;
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

    /// Get the type the instruction evaluates to.
    pub fn get_instruction_type(&self, id: MirInstructionId) -> &'mir MirType<'mir> {
        match self
            .get_instruction(id)
            .unwrap_or_else(|| ice!("missing instruction"))
        {
            MirInstruction::Alloca(i) => i.ty,
            MirInstruction::Store(i) => i.ty,
            MirInstruction::Call(i) => i.ty,
            MirInstruction::Load(i) => i.ty,
        }
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

    /// Get the type of the value with the given id.
    ///
    /// This function panics if the value does not exist.
    pub fn get_value_type(&self, id: MirValueId) -> &'mir MirType<'mir> {
        match self.get_value(id).unwrap_or_else(|| ice!("missing value")) {
            MirValue::ConstantInteger32(i) => i.ty,
            MirValue::ConstantBool(i) => i.ty,
            MirValue::Argument(a) => a.ty,
            MirValue::Instruction(i) => self.get_instruction_type(*i),
            MirValue::Function(_) | MirValue::Label(_) => unimplemented!(),
        }
    }
}

#[derive(Debug)]
pub struct MirFunction<'mir> {
    name: &'mir str,
    ty: &'mir MirFunctionType<'mir>,
    data: MirFunctionData<'mir>,
}

impl<'mir> MirFunction<'mir> {
    pub fn new(
        name: &'mir str,
        ty: &'mir MirFunctionType<'mir>,
        data: MirFunctionData<'mir>,
    ) -> Self {
        Self { name, ty, data }
    }

    /// Is the function expected to be resolved at link time?
    ///
    /// Functions with empty bodies are considered external.
    pub fn is_external(&self) -> bool {
        self.data.blocks.is_empty()
    }

    pub fn data(&self) -> &MirFunctionData<'mir> {
        &self.data
    }

    pub fn name(&self) -> &str {
        self.name
    }

    pub fn ty(&self) -> &MirFunctionType<'mir> {
        self.ty
    }
}
