use crate::mir::ty::MirType;
use crate::mir::value::MirValueId;
use std::ops::Deref;

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
        }
    }
}

/// The `mem.alloca` instruction.
#[derive(Debug)]
pub struct MirAllocaInstruction<'mir> {
    pub name: &'mir str,
    /// The type of the instruction itself. This is always the opaque pointer type for `mem.alloca`.
    pub ty: &'mir MirType<'mir>,
    /// The number (in bits) to allocate.
    pub alloc_size: usize,
    pub alloc_ty: &'mir MirType<'mir>,
}

/// The `mem.load` instruction.
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub name: &'mir str,
    /// The type being loaded
    pub ty: &'mir MirType<'mir>,
    pub src: MirValueId,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
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
    pub name: &'mir str,
    pub lhs: MirValueId,
    pub rhs: MirValueId,
    pub ty: &'mir MirType<'mir>,
}
