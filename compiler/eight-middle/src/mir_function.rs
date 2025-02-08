use crate::context::CompileContext;
use crate::mir::{
    MirAddInstruction, MirAllocaInstruction, MirArgument, MirCallInstruction, MirConstantBool,
    MirConstantInteger32, MirDivInstruction, MirFunctionType, MirInstruction, MirInstructionRef,
    MirLoadInstruction, MirMulInstruction, MirPtrAddInstruction, MirStoreInstruction,
    MirSubInstruction, MirTy, MirValue, MirValueRef,
};
use crate::mir_block::{MirBasicBlock, MirBasicBlockRef};
use crate::mir_module::MirModuleContext;
use eight_diagnostics::ice;
use std::collections::{BTreeMap, BTreeSet};

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
pub struct MirFunctionRef(usize);

impl MirFunctionRef {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn id(&self) -> usize {
        self.0
    }
}

#[derive(Debug, Default)]
pub struct MirFunctionData<'mir> {
    blocks: BTreeMap<MirBasicBlockRef, MirBasicBlock<'mir>>,
    block_instructions: BTreeMap<MirBasicBlockRef, BTreeSet<MirInstructionRef>>,
    values: BTreeMap<MirValueRef, MirValue<'mir>>,
    instructions: BTreeMap<MirInstructionRef, MirInstruction<'mir>>,
}

impl<'mir> MirFunctionData<'mir> {
    /// Get the block with the given id, or panic if it does not exist.
    fn get_expected_block(&self, block: &MirBasicBlockRef) -> &MirBasicBlock<'mir> {
        self.blocks
            .get(block)
            .unwrap_or_else(|| ice!("missing block {}", block.id()))
    }

    /// Get the instruction with the given id, or panic if it does not exist.
    fn get_expected_instruction(&self, instruction: &MirInstructionRef) -> &MirInstruction<'mir> {
        self.instructions
            .get(instruction)
            .unwrap_or_else(|| ice!("missing instruction {}", instruction.id()))
    }

    /// Get the block instructions with the given id, or panic if it does not exist.
    fn get_expected_block_instructions(
        &self,
        block: &MirBasicBlockRef,
    ) -> &BTreeSet<MirInstructionRef> {
        self.block_instructions
            .get(block)
            .unwrap_or_else(|| ice!("missing block {}", block.id()))
    }

    /// Get the value with the given id, or panic if it does not exist.
    fn get_expected_value(&self, value: &MirValueRef) -> &MirValue<'mir> {
        self.values
            .get(value)
            .unwrap_or_else(|| ice!("missing value {}", value.0))
    }
}

impl<'mir> MirFunctionData<'mir> {
    /// Get the instruction with the given id.
    pub fn get_instruction(&self, id: &MirInstructionRef) -> &MirInstruction<'mir> {
        self.get_expected_instruction(id)
    }

    /// Get an iterator over the instructions in the given block.
    ///
    /// TODO: Evaluate the performance of this function.
    pub fn get_block_instructions(
        &self,
        block: &MirBasicBlockRef,
    ) -> impl Iterator<Item = &MirInstruction<'mir>> {
        self.get_expected_block_instructions(block)
            .iter()
            .map(|i| self.get_instruction(i))
    }

    /// Get an iterator over the blocks in the function.
    ///
    /// TODO: Return these in topological order.
    pub fn get_blocks(&self) -> impl Iterator<Item = &MirBasicBlock<'mir>> {
        self.blocks.values()
    }

    /// Get the name of the given block.
    pub fn get_block(&self, block: &MirBasicBlockRef) -> &MirBasicBlock<'mir> {
        self.get_expected_block(block)
    }

    pub fn get_values(&self) -> impl Iterator<Item = &MirValue<'mir>> {
        self.values.values()
    }

    /// Get the value with the given id.
    pub fn get_value(&self, id: &MirValueRef) -> &MirValue<'mir> {
        self.get_expected_value(id)
    }

    /// Get the type of the value with the given id.
    pub fn get_value_type(&self, id: &MirValueRef) -> &'mir MirTy<'mir> {
        match self.get_value(id) {
            MirValue::ConstantInteger32(i) => i.ty,
            MirValue::ConstantBool(i) => i.ty,
            MirValue::Argument(a) => a.ty,
            MirValue::Instruction(i) => self.get_expected_instruction(i).ty(),
            MirValue::Function(_) | MirValue::Label(_) => unimplemented!(),
        }
    }
}

/// A builder for MIR functions.
///
/// A MIR builder is responsible for building a complete MIR function.
pub struct MirFunctionBuilder<'mir> {
    id: MirFunctionRef,
    cc: &'mir CompileContext<'mir>,
    ty: &'mir MirFunctionType<'mir>,
    name: &'mir str,
    data: MirFunctionData<'mir>,
    block_id: usize,
    value_id: usize,
    instruction_id: usize,
    /// The insertion point for the next instruction.
    insertion_point: Option<MirBasicBlockRef>,
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Create a new MIR function builder based on a signature.
    pub fn new(
        cc: &'mir CompileContext<'mir>,
        name: &'mir str,
        ty: &'mir MirFunctionType<'mir>,
        id: MirFunctionRef,
    ) -> Self {
        Self {
            id,
            ty,
            name,
            cc,
            data: MirFunctionData::default(),
            block_id: 0,
            value_id: 0,
            instruction_id: 0,
            insertion_point: None,
        }
    }

    pub fn data(&self) -> &MirFunctionData<'mir> {
        &self.data
    }

    /// Complete the function and consume the builder.
    pub fn build<'o>(self) -> MirFunction<'o>
    where
        'mir: 'o,
    {
        MirFunction::new(self.name, self.ty, self.data)
    }

    /// Create a new basic block
    pub fn build_basic_block(&mut self, name: Option<&'mir str>) -> MirBasicBlockRef {
        let id = self.block_id;
        let name = name.unwrap_or_else(|| self.cc.intern_as_str(id));
        let id = MirBasicBlockRef::new(id);
        let block = MirBasicBlock::new(id, name);
        self.data.blocks.insert(id, block);
        self.block_id += 1;
        id
    }

    /// Get the next instruction id.
    fn get_next_instruction_id(&self) -> MirInstructionRef {
        MirInstructionRef::new(self.instruction_id)
    }

    /// Build an instruction.
    ///
    /// This function doesn't actually build the instruction, but it moves ownership of the
    /// instruction into the builder, and returns the instruction ref.
    fn build_instruction(
        &mut self,
        id: MirInstructionRef,
        instruction: MirInstruction<'mir>,
    ) -> MirInstructionRef {
        self.data.instructions.insert(id, instruction);
        self.instruction_id += 1;
        id
    }

    /// Get the next value id.
    fn get_next_value_id(&self) -> MirValueRef {
        MirValueRef(self.value_id)
    }

    /// Build a value.
    ///
    /// This function doesn't actually build the value, but it moves ownership of the value into the
    /// builder, and returns the value id.
    fn build_value(&mut self, id: MirValueRef, kind: MirValue<'mir>) -> MirValueRef {
        self.data.values.insert(id, kind);
        self.value_id += 1;
        id
    }

    /// Insert the given instruction at the insertion point.
    ///
    /// This assumes that the instruction is allocated for the current function.
    fn insert(&mut self, instruction: MirInstructionRef) {
        let block = self.insertion_point.unwrap_or_else(|| {
            ice!("cannot insert instruction without a selected block");
        });
        self.data
            .block_instructions
            .entry(block)
            .or_default()
            .insert(instruction);
    }

    /// Set the insertion point to the given basic block id.
    pub fn move_insertion_point(&mut self, block: MirBasicBlockRef) {
        self.insertion_point = Some(block);
    }
}

impl<'mir> MirFunctionBuilder<'mir> {
    /// Build a constant integer value.
    pub fn build_constant_integer32(&mut self, value: i32, ty: &'mir MirTy<'mir>) -> MirValueRef {
        let value_id = self.get_next_value_id();
        let inst = MirValue::ConstantInteger32(MirConstantInteger32 {
            value_id,
            value,
            ty,
        });
        self.build_value(value_id, inst)
    }

    pub fn build_constant_bool(&mut self, value: bool, ty: &'mir MirTy<'mir>) -> MirValueRef {
        let value_id = self.get_next_value_id();
        let inst = MirValue::ConstantBool(MirConstantBool {
            value_id,
            value,
            ty,
        });
        self.build_value(value_id, inst)
    }

    /// Build an argument value
    pub fn build_argument(&mut self, name: &'mir str, ty: &'mir MirTy<'mir>) -> MirValueRef {
        let value_id = self.get_next_value_id();
        let inst = MirValue::Argument(MirArgument { value_id, name, ty });
        self.build_value(value_id, inst)
    }

    /// Build a reference to a function value.
    pub fn build_function_ref(&mut self, id: MirFunctionRef) -> MirValueRef {
        let value_id = self.get_next_value_id();
        let inst = MirValue::Function(id);
        self.build_value(value_id, inst)
    }

    /// Build a `mem.alloca` instruction.
    pub fn build_alloca<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Alloca(MirAllocaInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            ty: self.cc.mir_pointer_type(),
            alloc_ty: ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build a `mem.store` instruction.
    pub fn build_store<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        value: MirValueRef,
        dest: MirValueRef,
        name: Option<&'mir str>,
    ) -> MirInstructionRef {
        let inst_id = self.get_next_instruction_id();
        let inst = MirInstruction::Store(MirStoreInstruction {
            inst_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            ty: self.cc.mir_void_type(),
            // Stores are always into pointer types
            dest_ty: self.data.get_value_type(&value),
            value,
            dest,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        inst_id
    }

    /// Build a `mem.load` instruction.
    pub fn build_load<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        src: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Load(MirLoadInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            ty,
            src,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build a `fn.call` instruction.
    pub fn build_call<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        callee: MirValueRef,
        arguments: Vec<MirValueRef>,
        return_ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Call(MirCallInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            callee,
            arguments,
            ty: return_ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build an `arith.add` instruction.
    pub fn build_add<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        lhs: MirValueRef,
        rhs: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Add(MirAddInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            lhs,
            rhs,
            ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build an `arith.sub` instruction.
    pub fn build_sub<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        lhs: MirValueRef,
        rhs: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Sub(MirSubInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            lhs,
            rhs,
            ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build an `arith.mul` instruction.
    pub fn build_mul<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        lhs: MirValueRef,
        rhs: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Mul(MirMulInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            lhs,
            rhs,
            ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Build an `arith.div` instruction.
    pub fn build_div<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        lhs: MirValueRef,
        rhs: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Div(MirDivInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            lhs,
            rhs,
            ty,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    /// Arithmetic negation is re-written as subtraction from zero.
    pub fn build_neg<'hir>(
        &mut self,
        _: &MirModuleContext<'mir, 'hir>,
        input: MirValueRef,
        ty: &'mir MirTy<'mir>,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let zero = self.build_constant_integer32(0, self.cc.mir_i32_type());
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = MirInstruction::Sub(MirSubInstruction {
            inst_id,
            value_id,
            name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
            ty,
            lhs: zero,
            rhs: input,
        });
        let inst = self.build_instruction(inst_id, inst);
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }

    pub fn build_ptr_add_instruction(
        &mut self,
        ptr: MirValueRef,
        offset: MirValueRef,
        name: Option<&'mir str>,
    ) -> MirValueRef {
        let inst_id = self.get_next_instruction_id();
        let value_id = self.get_next_value_id();
        let inst = self.build_instruction(
            inst_id,
            MirInstruction::PtrAdd(MirPtrAddInstruction {
                inst_id,
                value_id,
                name: name.unwrap_or_else(|| self.cc.intern_as_str(inst_id.id())),
                ty: self.cc.mir_pointer_type(),
                ptr,
                offset,
            }),
        );
        self.insert(inst);
        self.build_value(value_id, MirValue::Instruction(inst))
    }
}
