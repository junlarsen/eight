use eight_diagnostics::ice;
use std::collections::BTreeMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Deref;

#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    pub functions: BTreeMap<MirFunctionId, MirFunction<'mir>>,
    pub function_types: BTreeMap<MirFunctionId, &'mir MirFunctionType<'mir>>,
    pub function_names: BTreeMap<MirFunctionId, &'mir str>,
    pub function_names_reverse: BTreeMap<&'mir str, MirFunctionId>,
}

impl<'mir> MirModuleData<'mir> {
    pub fn functions(&self) -> impl Iterator<Item = &MirFunction<'mir>> {
        self.functions.values()
    }

    pub fn get_function_by_id(&self, id: MirFunctionId) -> Option<&MirFunction<'mir>> {
        self.functions.get(&id)
    }

    pub fn get_function_by_name(&self, name: &'mir str) -> Option<&MirFunction<'mir>> {
        self.functions.get(self.function_names_reverse.get(name)?)
    }

    /// Get the function id for the given name.
    pub fn get_function_id(&self, name: &'mir str) -> Option<MirFunctionId> {
        self.function_names_reverse.get(name).copied()
    }

    /// Get the function name for the given id.
    pub fn get_function_name(&self, id: MirFunctionId) -> Option<&'mir str> {
        self.function_names.get(&id).copied()
    }

    /// Get the function type for the given id.
    pub fn get_function_type(&self, id: MirFunctionId) -> Option<&'mir MirFunctionType<'mir>> {
        self.function_types.get(&id).copied()
    }
}

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    data: MirModuleData<'mir>,
}

impl<'mir> MirModule<'mir> {
    pub fn new(data: MirModuleData<'mir>) -> Self {
        Self { data }
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MirTypeId(u64);

impl MirTypeId {
    pub fn compute_i32_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x00.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_bool_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x01.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_void_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x02.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_function_type_id(return_type: &MirTypeId, parameters: &[MirTypeId]) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x10, return_type, parameters).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_pointer_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        (0x20).hash(&mut hasher);
        Self(hasher.finish())
    }
}

impl<'mir> From<&'mir MirType<'mir>> for MirTypeId {
    fn from(ty: &'mir MirType<'mir>) -> Self {
        match ty {
            MirType::Integer32(_) => MirTypeId::compute_i32_type_id(),
            MirType::Bool(_) => MirTypeId::compute_bool_type_id(),
            MirType::Void(_) => MirTypeId::compute_void_type_id(),
            MirType::Pointer(ty) => MirTypeId::compute_pointer_type_id(),
            MirType::Function(ty) => {
                let parameters = ty
                    .parameters
                    .iter()
                    .map(|p| MirTypeId::from(*p))
                    .collect::<Vec<_>>();
                MirTypeId::compute_function_type_id(
                    &MirTypeId::from(ty.return_type),
                    parameters.as_slice(),
                )
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum MirType<'mir> {
    Integer32(MirInteger32Type),
    Bool(MirBoolType),
    Void(MirVoidType),
    Pointer(MirPointerType),
    Function(MirFunctionType<'mir>),
}

impl MirType<'_> {
    /// Get the size of the type in bytes.
    ///
    /// This is currently hard-coded for x86-64 and will need to be populated with target info once
    /// that has been added.
    pub fn get_size(&self) -> usize {
        match self {
            MirType::Integer32(_) => 32,
            MirType::Bool(_) => 1,
            MirType::Void(_) => 0,
            MirType::Pointer(_) => 64,
            MirType::Function(_) => unimplemented!(),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirInteger32Type;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirBoolType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirVoidType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirPointerType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirFunctionType<'mir> {
    pub return_type: &'mir MirType<'mir>,
    pub parameters: Vec<&'mir MirType<'mir>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirValueId(pub usize);

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[derive(Debug)]
pub enum MirValue<'mir> {
    ConstantInteger32(MirConstantInteger32<'mir>),
    ConstantBool(MirConstantBool<'mir>),
    Argument(MirArgument<'mir>),
    Instruction(MirInstructionId),
    Label(MirBasicBlockId),
    Function(MirFunctionId),
}

#[derive(Debug)]
pub struct MirConstantInteger32<'mir> {
    pub value_id: MirValueId,
    pub ty: &'mir MirType<'mir>,
    pub value: i32,
}

#[derive(Debug)]
pub struct MirConstantBool<'mir> {
    pub value_id: MirValueId,
    pub ty: &'mir MirType<'mir>,
    pub value: bool,
}

#[derive(Debug)]
pub struct MirArgument<'mir> {
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirInstructionId(pub usize);

impl Deref for MirInstructionId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
pub enum MirInstruction<'mir> {
    Alloca(MirAllocaInstruction<'mir>),
    Load(MirLoadInstruction<'mir>),
    Store(MirStoreInstruction<'mir>),
    Call(MirCallInstruction<'mir>),
    Add(MirAddInstruction<'mir>),
    Sub(MirSubInstruction<'mir>),
    Mul(MirMulInstruction<'mir>),
    Div(MirDivInstruction<'mir>),
    PtrAdd(MirPtrAddInstruction<'mir>),
}

impl<'mir> MirInstruction<'mir> {
    pub fn ty(&self) -> &'mir MirType<'mir> {
        match self {
            MirInstruction::Alloca(i) => i.ty,
            MirInstruction::Load(i) => i.ty,
            MirInstruction::Store(i) => i.ty,
            MirInstruction::Call(i) => i.ty,
            MirInstruction::Add(i) => i.ty,
            MirInstruction::Sub(i) => i.ty,
            MirInstruction::Mul(i) => i.ty,
            MirInstruction::Div(i) => i.ty,
            MirInstruction::PtrAdd(i) => i.ty,
        }
    }
}

/// The `mem.alloca` instruction.
#[derive(Debug)]
pub struct MirAllocaInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    /// The type of the instruction itself. This is always the opaque pointer type for `mem.alloca`.
    pub ty: &'mir MirType<'mir>,
    /// The number (in bits) to allocate.
    pub alloc_ty: &'mir MirType<'mir>,
}

/// The `mem.load` instruction.
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub value_id: MirValueId,
    pub inst_id: MirInstructionId,
    pub name: &'mir str,
    /// The type being loaded
    pub ty: &'mir MirType<'mir>,
    pub src: MirValueId,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub name: &'mir str,
    pub value: MirValueId,
    /// The result of a store is always void
    pub ty: &'mir MirType<'mir>,
    pub dest: MirValueId,
    pub dest_ty: &'mir MirType<'mir>,
}

/// The `fn.call` instruction.
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub callee: MirValueId,
    pub arguments: Vec<MirValueId>,
    /// The return type of the function.
    pub ty: &'mir MirType<'mir>,
}

/// The `arith.add` instruction.
///
/// # Lowering rules
///
/// This function only works on compiler intrinsic additions. In practice, it means that trait
/// instances of `Add` are lowered into a call instruction unless they are implemented as a compiler
/// intrinsic.
#[derive(Debug)]
pub struct MirAddInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub lhs: MirValueId,
    pub rhs: MirValueId,
    pub ty: &'mir MirType<'mir>,
}

/// The `arith.sub` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirSubInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub lhs: MirValueId,
    pub rhs: MirValueId,
    pub ty: &'mir MirType<'mir>,
}

/// The `arith.mul` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirMulInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub lhs: MirValueId,
    pub rhs: MirValueId,
    pub ty: &'mir MirType<'mir>,
}

/// The `arith.div` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirDivInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub lhs: MirValueId,
    pub rhs: MirValueId,
    pub ty: &'mir MirType<'mir>,
}

/// The `ptr.add` instruction.
///
/// The `ptr.add` instruction adds an offset to a pointer, useful for calculating the address of a
/// field in a struct or general pointer arithmetic.
#[derive(Debug)]
pub struct MirPtrAddInstruction<'mir> {
    pub inst_id: MirInstructionId,
    pub value_id: MirValueId,
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
    pub ptr: MirValueId,
    pub offset: MirValueId,
}

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

impl MirBasicBlock<'_> {
    pub fn insert(&mut self, instruction: MirInstructionId) {
        self.instructions.push(instruction);
    }
}
