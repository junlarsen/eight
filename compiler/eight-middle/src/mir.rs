use eight_macros::declare_ref_type;
use std::hash::{DefaultHasher, Hash, Hasher};

declare_ref_type!(MirFunctionRef, usize);
declare_ref_type!(MirBasicBlockRef, usize);
declare_ref_type!(MirInstructionRef, usize);
declare_ref_type!(MirValueRef, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MirTyId(u64);

impl MirTyId {
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

    pub fn compute_function_type_id(return_type: &MirTyId, parameters: &[MirTyId]) -> Self {
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

impl<'mir> From<&'mir MirTy<'mir>> for MirTyId {
    fn from(ty: &'mir MirTy<'mir>) -> Self {
        match ty {
            MirTy::Integer32(_) => MirTyId::compute_i32_type_id(),
            MirTy::Bool(_) => MirTyId::compute_bool_type_id(),
            MirTy::Void(_) => MirTyId::compute_void_type_id(),
            MirTy::Pointer(_) => MirTyId::compute_pointer_type_id(),
            MirTy::Function(ty) => {
                let parameters = ty
                    .parameters
                    .iter()
                    .map(|p| MirTyId::from(*p))
                    .collect::<Vec<_>>();
                MirTyId::compute_function_type_id(
                    &MirTyId::from(ty.return_type),
                    parameters.as_slice(),
                )
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum MirTy<'mir> {
    Integer32(MirInteger32Type),
    Bool(MirBoolType),
    Void(MirVoidType),
    Pointer(MirPointerType),
    Function(MirFunctionType<'mir>),
}

impl MirTy<'_> {
    /// Get the size of the type in bytes.
    ///
    /// This is currently hard-coded for x86-64 and will need to be populated with target info once
    /// that has been added.
    pub fn get_size(&self) -> usize {
        match self {
            MirTy::Integer32(_) => 32,
            MirTy::Bool(_) => 1,
            MirTy::Void(_) => 0,
            MirTy::Pointer(_) => 64,
            MirTy::Function(_) => unimplemented!(),
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
    pub return_type: &'mir MirTy<'mir>,
    pub parameters: Vec<&'mir MirTy<'mir>>,
}

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[derive(Debug)]
pub enum MirValue<'mir> {
    ConstantInteger32(MirConstantInteger32<'mir>),
    ConstantBool(MirConstantBool<'mir>),
    Argument(MirArgument<'mir>),
    Instruction(MirInstructionRef),
    Label(MirBasicBlockRef),
    Function(MirFunctionRef),
}

#[derive(Debug)]
pub struct MirConstantInteger32<'mir> {
    pub value_id: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
    pub value: i32,
}

#[derive(Debug)]
pub struct MirConstantBool<'mir> {
    pub value_id: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
    pub value: bool,
}

#[derive(Debug)]
pub struct MirArgument<'mir> {
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub ty: &'mir MirTy<'mir>,
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
    pub fn ty(&self) -> &'mir MirTy<'mir> {
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

    pub fn instruction_id(&self) -> &MirInstructionRef {
        match self {
            MirInstruction::Alloca(i) => &i.inst_id,
            MirInstruction::Load(i) => &i.inst_id,
            MirInstruction::Store(i) => &i.inst_id,
            MirInstruction::Call(i) => &i.inst_id,
            MirInstruction::Add(i) => &i.inst_id,
            MirInstruction::Sub(i) => &i.inst_id,
            MirInstruction::Mul(i) => &i.inst_id,
            MirInstruction::Div(i) => &i.inst_id,
            MirInstruction::PtrAdd(i) => &i.inst_id,
        }
    }
}

/// The `mem.alloca` instruction.
#[derive(Debug)]
pub struct MirAllocaInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    /// The type of the instruction itself. This is always the opaque pointer type for `mem.alloca`.
    pub ty: &'mir MirTy<'mir>,
    /// The number (in bits) to allocate.
    pub alloc_ty: &'mir MirTy<'mir>,
}

/// The `mem.load` instruction.
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub value_id: MirValueRef,
    pub inst_id: MirInstructionRef,
    pub name: &'mir str,
    /// The type being loaded
    pub ty: &'mir MirTy<'mir>,
    pub src: MirValueRef,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub name: &'mir str,
    pub value: MirValueRef,
    /// The result of a store is always void
    pub ty: &'mir MirTy<'mir>,
    pub dest: MirValueRef,
    pub dest_ty: &'mir MirTy<'mir>,
}

/// The `fn.call` instruction.
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub callee: MirValueRef,
    pub arguments: Vec<MirValueRef>,
    /// The return type of the function.
    pub ty: &'mir MirTy<'mir>,
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
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub lhs: MirValueRef,
    pub rhs: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
}

/// The `arith.sub` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirSubInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub lhs: MirValueRef,
    pub rhs: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
}

/// The `arith.mul` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirMulInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub lhs: MirValueRef,
    pub rhs: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
}

/// The `arith.div` instruction.
///
/// Same lowering rules as `MirAddInstruction`.
#[derive(Debug)]
pub struct MirDivInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub lhs: MirValueRef,
    pub rhs: MirValueRef,
    pub ty: &'mir MirTy<'mir>,
}

/// The `ptr.add` instruction.
///
/// The `ptr.add` instruction adds an offset to a pointer, useful for calculating the address of a
/// field in a struct or general pointer arithmetic.
#[derive(Debug)]
pub struct MirPtrAddInstruction<'mir> {
    pub inst_id: MirInstructionRef,
    pub value_id: MirValueRef,
    pub name: &'mir str,
    pub ty: &'mir MirTy<'mir>,
    pub ptr: MirValueRef,
    pub offset: MirValueRef,
}
