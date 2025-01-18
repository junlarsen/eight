use crate::instruction::{MirCallInstruction, MirLoadInstruction, MirStoreInstruction};
use crate::ty::MirType;

/// Anything that can be referenced as a value in the MIR.
#[derive(Debug)]
pub struct MirValue<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub val: MirValueKind<'mir>,
}

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[derive(Debug)]
pub enum MirValueKind<'mir> {
    ConstantInteger(MirConstantInteger<'mir>),
    LoadInstruction(MirLoadInstruction<'mir>),
    StoreInstruction(MirStoreInstruction<'mir>),
    CallInstruction(MirCallInstruction<'mir>),
    Local(MirLocal<'mir>),
    Argument(MirArgument<'mir>),
}

#[derive(Debug)]
pub struct MirConstantInteger<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub value: i64,
}

#[derive(Debug)]
pub struct MirLocal<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
}

#[derive(Debug)]
pub struct MirArgument<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
}
