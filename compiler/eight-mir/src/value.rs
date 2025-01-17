use crate::instruction::MirLoadInstruction;
use crate::MirType;

/// Anything that can be referenced as a value in the MIR.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirValue {
    pub ty: MirType,
}

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum MirValueKind {
    ConstantInteger(MirConstantInteger),
    LoadInstruction(MirLoadInstruction),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirConstantInteger {
    pub ty: MirType,
    pub value: i64,
}
