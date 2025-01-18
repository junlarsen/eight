use crate::ty::MirType;
use crate::value::{MirLocal, MirValue};

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
    pub ty: &'mir MirType<'mir>,
    pub size: i32,
}

/// The `mem.load` instruction.
#[derive(Debug)]
pub struct MirLoadInstruction<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub src: MirLocal<'mir>,
}

/// The `mem.store` instruction.
#[derive(Debug)]
pub struct MirStoreInstruction<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub value: Box<MirValue<'mir>>,
    pub dest: MirLocal<'mir>,
}

/// The `fn.call` instruction.
#[derive(Debug)]
pub struct MirCallInstruction<'mir> {
    pub callee: &'mir str,
    pub arguments: Vec<MirValue<'mir>>,
}
