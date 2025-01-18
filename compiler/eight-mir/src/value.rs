use crate::builder::{MirFunctionBuilder, MirModuleContext};
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

impl<'mir> MirValue<'mir> {
    pub fn ty(
        &self,
        b: &MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, '_>,
    ) -> &'mir MirType<'mir> {
        match self {
            MirValue::ConstantInteger(i) => i.ty,
            MirValue::Argument(a) => a.ty,
            MirValue::Instruction(i) => b.get_instruction(*i).expect("missing instruction").ty(),
            MirValue::Function(f) => {
                cx.get_function_type(*f)
                    .expect("missing function type")
                    .return_type
            }
            MirValue::Label(_) => unimplemented!(),
        }
    }
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
