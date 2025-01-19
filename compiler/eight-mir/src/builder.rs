use crate::arena::MirArena;
use crate::function::{MirFunction, MirFunctionData};
use crate::instruction::{
    MirAllocaInstruction, MirCallInstruction, MirInstruction, MirInstructionId, MirLoadInstruction,
    MirStoreInstruction,
};
use crate::ty::{MirFunctionType, MirType};
use crate::value::{MirArgument, MirConstantBool, MirConstantInteger32, MirValue, MirValueId};
use crate::{MirBasicBlock, MirBasicBlockId, MirFunctionId, MirModule, MirModuleData};
use eight_diagnostics::ice;
use eight_hir::HirModule;

pub struct MirModuleContext<'mir, 'hir> {
    arena: &'mir MirArena<'mir>,
    hir_module: &'hir HirModule<'hir>,
    data: MirModuleData<'mir>,
    function_id: usize,
}

impl<'mir, 'hir> MirModuleContext<'mir, 'hir> {
    pub fn new(arena: &'mir MirArena<'mir>, hir_module: &'hir HirModule<'hir>) -> Self {
        Self {
            arena,
            hir_module,
            function_id: 0,
            data: MirModuleData::default(),
        }
    }

    pub fn build(self) -> MirModule<'mir> {
        MirModule { data: self.data }
    }

    /// Reserve the next function id.
    pub fn forward_declare_function(
        &mut self,
        name: &str,
        ty: &'mir MirFunctionType<'mir>,
    ) -> MirFunctionId {
        let name = self.arena.names().get(name);
        let id = MirFunctionId(self.function_id);
        self.function_id += 1;
        self.data.function_names.insert(id, name);
        self.data.function_types.insert(id, ty);
        self.data.function_names_reverse.insert(name, id);
        id
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }

    /// Provide the completed MIR function.
    pub fn implement_function(&mut self, id: MirFunctionId, fun: MirFunction<'mir>) {
        if self.data.functions.contains_key(&id) {
            ice!("function already implemented");
        }
        self.data.functions.insert(id, fun);
    }
}

/// A builder for MIR functions.
///
/// A MIR builder is responsible for building a complete MIR function.
pub struct MirFunctionBuilder<'mir> {
    id: MirFunctionId,
    arena: &'mir MirArena<'mir>,
    ty: &'mir MirFunctionType<'mir>,
    name: &'mir str,
    data: MirFunctionData<'mir>,
    block_id: usize,
    value_id: usize,
    instruction_id: usize,
    /// The insertion point for the next instruction.
    insertion_point: Option<MirBasicBlockId>,
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Create a new MIR function builder based on a signature.
    pub fn new(
        arena: &'mir MirArena<'mir>,
        name: &'mir str,
        ty: &'mir MirFunctionType<'mir>,
        id: MirFunctionId,
    ) -> Self {
        Self {
            id,
            ty,
            name,
            arena,
            data: MirFunctionData::default(),
            block_id: 0,
            value_id: 0,
            instruction_id: 0,
            insertion_point: None,
        }
    }

    /// Complete the function and consume the builder.
    pub fn build<'o>(self) -> MirFunction<'o>
    where
        'mir: 'o,
    {
        MirFunction::new(self.name, self.ty, self.data)
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
        self.data.blocks.insert(id, block);
        self.block_id += 1;
        id
    }

    pub fn get_basic_block(&self, id: MirBasicBlockId) -> Option<&MirBasicBlock<'mir>> {
        self.data.blocks.get(&id)
    }

    /// Get the next instruction id.
    fn get_next_instruction_id(&self) -> MirInstructionId {
        MirInstructionId(self.instruction_id)
    }

    /// Build an instruction.
    ///
    /// This function doesn't actually build the instruction, but it moves ownership of the
    /// instruction into the builder, and returns the instruction ref.
    fn build_instruction(
        &mut self,
        id: MirInstructionId,
        instruction: MirInstruction<'mir>,
    ) -> MirInstructionId {
        self.data.instructions.insert(id, instruction);
        self.instruction_id += 1;
        id
    }

    pub fn get_instruction(&self, id: MirInstructionId) -> Option<&MirInstruction<'mir>> {
        self.data.instructions.get(&id)
    }

    /// Build a value.
    ///
    /// This function doesn't actually build the value, but it moves ownership of the value into the
    /// builder, and returns the value id.
    fn build_value(&mut self, kind: MirValue<'mir>) -> MirValueId {
        let id = self.value_id;
        let id = MirValueId(id);
        self.data.values.insert(id, kind);
        self.value_id += 1;
        id
    }

    pub fn get_value(&self, id: MirValueId) -> Option<&MirValue<'mir>> {
        self.data.values.get(&id)
    }

    /// Get a mutable reference to the insertion point.
    fn insertion_point_mut<'c>(&'c mut self) -> &'c mut MirBasicBlock<'mir> {
        let insertion_point = self.insertion_point.unwrap_or_else(|| {
            ice!("cannot get insertion point without a selected block");
        });
        self.data
            .blocks
            .get_mut(&insertion_point)
            .unwrap_or_else(|| {
                ice!("insertion point is out of bounds");
            })
    }

    /// Set the insertion point to the given basic block id.
    pub fn move_insertion_point(&mut self, block: MirBasicBlockId) {
        self.insertion_point = Some(block);
    }
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Build a constant integer value.
    pub fn build_constant_integer32(&mut self, value: i32, ty: &'mir MirType<'mir>) -> MirValueId {
        let inst = MirValue::ConstantInteger32(MirConstantInteger32 { value, ty });
        self.build_value(inst)
    }

    pub fn build_constant_bool(&mut self, value: bool, ty: &'mir MirType<'mir>) -> MirValueId {
        let inst = MirValue::ConstantBool(MirConstantBool { value, ty });
        self.build_value(inst)
    }

    /// Build an argument value
    pub fn build_argument(&mut self, name: &'mir str, ty: &'mir MirType<'mir>) -> MirValueId {
        let inst = MirValue::Argument(MirArgument { name, ty });
        self.build_value(inst)
    }

    /// Build a reference to a function value.
    pub fn build_function_ref(&mut self, id: MirFunctionId) -> MirValueId {
        let inst = MirValue::Function(id);
        self.build_value(inst)
    }

    /// Build a `mem.alloca` instruction.
    pub fn build_alloca<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        ty: &'mir MirType<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let id = self.get_next_instruction_id();
        let inst = MirInstruction::Alloca(MirAllocaInstruction {
            name: name.unwrap_or_else(|| self.arena.names().get_usize(*id)),
            // `mem.alloca` always yields a pointer type.
            ty: self.arena.types().get_pointer_type(ty),
            alloc_size: ty.get_size(),
            alloc_ty: ty,
        });
        let inst = self.build_instruction(id, inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }

    /// Build a `mem.store` instruction.
    pub fn build_store<'hir>(
        &mut self,
        cx: &MirModuleContext<'mir, 'hir>,
        value: MirValueId,
        dest: MirValueId,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let id = self.get_next_instruction_id();
        let v = self.get_value(value).unwrap_or_else(|| {
            ice!("failed to find value for store");
        });

        let inst = MirInstruction::Store(MirStoreInstruction {
            name: name.unwrap_or_else(|| self.arena.names().get_usize(*id)),
            ty: self.arena.types().get_void_type(),
            // Stores are always into pointer types
            dest_ty: v.ty(self, cx),
            value,
            dest,
        });
        let inst = self.build_instruction(id, inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }

    /// Build a `mem.load` instruction.
    pub fn build_load<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        src: MirValueId,
        ty: &'mir MirType<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let id = self.get_next_instruction_id();
        let inst = MirInstruction::Load(MirLoadInstruction {
            name: name.unwrap_or_else(|| self.arena.names().get_usize(*id)),
            ty,
            src,
        });
        let inst = self.build_instruction(id, inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }

    /// Build a `fn.call` instruction.
    pub fn build_call<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        callee: MirValueId,
        arguments: Vec<MirValueId>,
        return_ty: &'mir MirType<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueId {
        let id = self.get_next_instruction_id();
        let inst = MirInstruction::Call(MirCallInstruction {
            name: name.unwrap_or_else(|| self.arena.names().get_usize(*id)),
            callee,
            arguments,
            ty: return_ty,
        });
        let inst = self.build_instruction(id, inst);
        self.insertion_point_mut().insert(inst);
        self.build_value(MirValue::Instruction(inst))
    }
}
