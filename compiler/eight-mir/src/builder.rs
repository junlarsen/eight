use crate::arena::MirArena;
use crate::instruction::{
    MirAllocaInstruction, MirInstruction, MirInstructionId, MirLoadInstruction, MirStoreInstruction,
};
use crate::ty::{MirFunctionType, MirType};
use crate::value::{MirArgument, MirConstantInteger, MirValue, MirValueId};
use crate::{MirBasicBlock, MirBasicBlockId, MirFunction};
use eight_diagnostics::ice;
use std::collections::BTreeMap;

/// A builder for MIR functions.
///
/// A MIR builder is responsible for building a complete MIR function.
pub struct MirFunctionBuilder<'mir> {
    arena: &'mir MirArena<'mir>,
    ty: &'mir MirFunctionType<'mir>,
    name: &'mir str,
    /// List of basic blocks built for the function.
    blocks: BTreeMap<MirBasicBlockId, MirBasicBlock<'mir>>,
    block_id: usize,

    /// List of values built for the function.
    values: BTreeMap<MirValueId, MirValue<'mir>>,
    value_id: usize,

    /// List of instructions built for the function.
    instructions: BTreeMap<MirInstructionId, MirInstruction<'mir>>,
    instruction_id: usize,
    /// The insertion point for the next instruction.
    insertion_point: Option<MirBasicBlockId>,
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Create a new MIR function builder based on a signature.
    pub fn new(
        arena: &'mir MirArena<'mir>,
        ty: &'mir MirFunctionType<'mir>,
        name: &'mir str,
    ) -> Self {
        Self {
            arena,
            ty,
            name,
            blocks: BTreeMap::new(),
            block_id: 0,
            values: BTreeMap::new(),
            value_id: 0,
            instructions: BTreeMap::new(),
            instruction_id: 0,
            insertion_point: None,
        }
    }

    /// Complete the function and consume the builder.
    pub fn build(self) -> MirFunction<'mir> {
        MirFunction {
            ty: self.ty,
            name: self.name,
            blocks: self.blocks,
            values: self.values,
            instructions: self.instructions,
        }
    }
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Create a new basic block
    pub fn build_basic_block(&mut self, name: Option<&'mir str>) -> MirBasicBlockId {
        let id = self.block_id;
        let name = name.unwrap_or_else(|| self.arena.names().get_usize(id));
        let id = MirBasicBlockId(id);
        let block = MirBasicBlock {
            name,
            instructions: Vec::new(),
        };
        self.blocks.insert(id, block);
        self.block_id += 1;
        id
    }

    /// Build an instruction.
    ///
    /// This function doesn't actually build the instruction, but it moves ownership of the
    /// instruction into the builder, and returns the instruction ref.
    pub fn build_instruction(&mut self, instruction: MirInstruction<'mir>) -> MirInstructionId {
        let id = self.instruction_id;
        let id = MirInstructionId(id);
        self.instructions.insert(id, instruction);
        self.instruction_id += 1;
        id
    }

    /// Build a value.
    ///
    /// This function doesn't actually build the value, but it moves ownership of the value into the
    /// builder, and returns the value id.
    pub fn build_value(&mut self, kind: MirValue<'mir>) -> MirValueId {
        let id = self.value_id;
        let id = MirValueId(id);
        self.values.insert(id, kind);
        self.value_id += 1;
        id
    }

    /// Set the insertion point to the given basic block id.
    pub fn move_insertion_point(&mut self, block: MirBasicBlockId) {
        self.insertion_point = Some(block);
    }

    /// Get a mutable reference to the insertion point.
    fn insertion_point_mut<'c>(&'c mut self) -> &'c mut MirBasicBlock<'mir> {
        let insertion_point = self.insertion_point.unwrap_or_else(|| {
            ice!("cannot get insertion point without a selected block");
        });
        self.blocks.get_mut(&insertion_point).unwrap_or_else(|| {
            ice!("insertion point is out of bounds");
        })
    }
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Build a constant integer value.
    pub fn build_constant_integer(&mut self, value: i64, ty: &'mir MirType<'mir>) -> MirValueId {
        let inst = MirValue::ConstantInteger(MirConstantInteger { value, ty });
        self.build_value(inst)
    }

    /// Build an argument value
    pub fn build_argument(&mut self, name: &'mir str, ty: &'mir MirType<'mir>) -> MirValueId {
        let inst = MirValue::Argument(MirArgument { name, ty });
        self.build_value(inst)
    }

    /// Build a `mem.alloca` instruction.
    pub fn build_alloca(&mut self, ty: &'mir MirType<'mir>, name: Option<&'mir str>) -> MirValueId {
        let inst = MirInstruction::Alloca(MirAllocaInstruction {
            name,
            // `mem.alloca` always yields a pointer type.
            ty: self.arena.types().get_pointer_type(),
            alloc_size: ty.get_size(),
            alloc_ty: ty,
        });
        let inst = self.build_instruction(inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }

    /// Build a `mem.store` instruction.
    pub fn build_store(
        &mut self,
        value: MirValueId,
        dest: MirValueId,
        ty: &'mir MirType<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let inst = MirInstruction::Store(MirStoreInstruction {
            name,
            ty,
            value,
            dest,
        });
        let inst = self.build_instruction(inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }

    /// Build a `mem.load` instruction.
    pub fn build_load(
        &mut self,
        src: MirValueId,
        ty: &'mir MirType<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let inst = MirInstruction::Load(MirLoadInstruction { name, ty, src });
        let inst = self.build_instruction(inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }
}
