use crate::mir::bb::MirBasicBlockId;
use crate::mir::function::MirFunctionId;
use crate::mir::instruction::MirInstructionId;
use crate::mir::ty::MirType;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirValueId(pub usize);

/// The kind of value that is being referenced.
///
/// This is loosely modeled after the LLVM IR Value class.
#[derive(Debug)]
pub enum MirValue<'mir> {
    ConstantInteger32(MirConstantInteger32<'mir>),
    ConstantBool(MirConstantBool<'mir>),
    Argument(MirArgument<'mir>),
    Instruction(MirInstructionId),
    Label(MirBasicBlockId),
    Function(MirFunctionId),
}

#[derive(Debug)]
pub struct MirConstantInteger32<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub value: i32,
}

#[derive(Debug)]
pub struct MirConstantBool<'mir> {
    pub ty: &'mir MirType<'mir>,
    pub value: bool,
}

#[derive(Debug)]
pub struct MirArgument<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirType<'mir>,
}
