use crate::mir::bb::{MirBasicBlock, MirBasicBlockId};
use crate::mir::instruction::{MirInstruction, MirInstructionId};
use crate::mir::ty::{MirFunctionType, MirType};
use crate::mir::value::{MirValue, MirValueId};
use eight_diagnostics::ice;
use std::collections::BTreeMap;
use std::ops::Deref;

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
    pub fn get_instruction(&self, id: MirInstructionId) -> &MirInstruction<'mir> {
        self.instructions
            .get(&id)
            .unwrap_or_else(|| ice!(format!("missing instruction {}", id.0)))
    }

    /// Get the type the instruction evaluates to.
    pub fn get_instruction_type(&self, id: MirInstructionId) -> &'mir MirType<'mir> {
        self.get_instruction(id).ty()
    }

    pub fn blocks(&self) -> impl Iterator<Item = &MirBasicBlock<'mir>> {
        self.blocks.values()
    }

    /// Get the basic block with the given id.
    pub fn get_basic_block(&self, id: MirBasicBlockId) -> &MirBasicBlock<'mir> {
        self.blocks
            .get(&id)
            .unwrap_or_else(|| ice!(format!("missing block {}", id.0)))
    }

    pub fn values(&self) -> impl Iterator<Item = &MirValue<'mir>> {
        self.values.values()
    }

    /// Get the value with the given id.
    pub fn get_value(&self, id: MirValueId) -> &MirValue<'mir> {
        self.values
            .get(&id)
            .unwrap_or_else(|| ice!(format!("missing value {}", id.0)))
    }

    /// Get the type of the value with the given id.
    ///
    /// This function panics if the value does not exist.
    pub fn get_value_type(&self, id: MirValueId) -> &'mir MirType<'mir> {
        match self.get_value(id) {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirFunctionId(pub usize);

impl Deref for MirFunctionId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
