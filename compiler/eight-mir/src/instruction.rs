use crate::ty::MirType;
use crate::value::MirValueId;
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
    pub ty: &'mir MirType<'mir>,
    pub src: MirValueId,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub name: &'mir str,
    pub value: MirValueId,
    pub dest: MirValueId,
    pub dest_ty: &'mir MirType<'mir>,
}

/// The `fn.call` instruction.
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub name: &'mir str,
    pub callee: &'mir str,
    pub arguments: Vec<MirValueId>,
    pub return_ty: &'mir MirType<'mir>,
}
