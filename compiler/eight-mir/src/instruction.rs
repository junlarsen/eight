use crate::value::{MirLocal, MirValue};
use crate::MirType;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum MirInstruction<'mir> {
    Alloca(MirAllocaInstruction),
    Load(MirLoadInstruction<'mir>),
    Store(MirStoreInstruction<'mir>),
    Call(MirCallInstruction<'mir>),
}

/// The `mem.alloca` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirAllocaInstruction {
    pub ty: MirType,
    pub size: i32,
}

/// The `mem.load` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub ty: MirType,
    pub src: MirLocal<'mir>,
}

/// The `mem.store` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub ty: MirType,
    pub value: Box<MirValue<'mir>>,
    pub dest: MirLocal<'mir>,
}

/// The `fn.call` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub callee: &'mir str,
    pub arguments: Vec<MirValue<'mir>>,
}
