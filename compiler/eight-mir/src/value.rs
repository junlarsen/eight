use crate::instruction::{MirCallInstruction, MirLoadInstruction, MirStoreInstruction};
use crate::MirType;

/// Anything that can be referenced as a value in the MIR.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirValue<'mir> {
    pub ty: MirType,
    pub val: MirValueKind<'mir>,
}

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum MirValueKind<'mir> {
    ConstantInteger(MirConstantInteger),
    LoadInstruction(MirLoadInstruction<'mir>),
    StoreInstruction(MirStoreInstruction<'mir>),
    CallInstruction(MirCallInstruction<'mir>),
    Local(MirLocal<'mir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirConstantInteger {
    pub ty: MirType,
    pub value: i64,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirLocal<'mir> {
    pub name: &'mir str,
    pub ty: MirType,
}
