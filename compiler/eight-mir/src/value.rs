use crate::instruction::MirInstructionId;
use crate::ty::MirType;
use crate::{MirBasicBlockId, MirFunctionId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirValueId(pub usize);

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[derive(Debug)]
pub enum MirValue<'mir> {
    /// This is a constant integer value
    ConstantInteger(MirConstantInteger<'mir>),
    /// This is a function argument that was passed to the function.
    Argument(MirArgument<'mir>),
    /// This refers to an instruction.
    Instruction(MirInstructionId),
    /// This refers to the label of a basic block.
    Label(MirBasicBlockId),
    /// This refers to a named function
    Function(MirFunctionId),
}

#[derive(Debug)]
pub struct MirConstantInteger<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub value: i64,
}

#[derive(Debug)]
pub struct MirArgument<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
}
