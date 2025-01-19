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
    ConstantInteger32(MirConstantInteger32<'mir>),
    ConstantBool(MirConstantBool<'mir>),
    Argument(MirArgument<'mir>),
    Instruction(MirInstructionId),
    Label(MirBasicBlockId),
    Function(MirFunctionId),
}

impl<'mir> MirValue<'mir> {
    pub fn ty(
        &self,
        b: &MirFunctionBuilder<'mir>,
        cx: &MirModuleContext<'mir, '_>,
    ) -> &'mir MirType<'mir> {
        match self {
            MirValue::ConstantInteger32(i) => i.ty,
            MirValue::ConstantBool(i) => i.ty,
            MirValue::Argument(a) => a.ty,
            MirValue::Instruction(i) => b.get_instruction(*i).expect("missing instruction").ty(),
            MirValue::Function(f) => {
                cx.data().get_function_type(*f)
                    .expect("missing function type")
                    .return_type
            }
            MirValue::Label(_) => unimplemented!(),
        }
    }
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
