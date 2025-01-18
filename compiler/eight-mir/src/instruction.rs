use crate::ty::MirType;
use crate::value::MirValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirInstructionId(pub usize);

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
    pub name: Option<&'mir str>,
    /// The type of the instruction itself. This is always the opaque pointer type for `mem.alloca`.
    pub ty: &'mir MirType<'mir>,
    /// The number (in bits) to allocate.
    pub alloc_size: usize,
    pub alloc_ty: &'mir MirType<'mir>,
}

/// The `mem.load` instruction.
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub name: Option<&'mir str>,
    pub ty: &'mir MirType<'mir>,
    pub src: MirValueId,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub name: Option<&'mir str>,
    pub ty: &'mir MirType<'mir>,
    pub value: MirValueId,
    pub dest: MirValueId,
}

/// The `fn.call` instruction.
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub name: Option<&'mir str>,
    pub callee: &'mir str,
    pub arguments: MirValueId,
}
