use eight_macros::declare_error_type;
use inkwell::builder::BuilderError;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("codegen error: {0}")]
    pub enum LLVMBackendError {
        LLVMBuilderError(LLVMBuilderError),
    }
}

impl From<BuilderError> for LLVMBackendError {
    fn from(e: BuilderError) -> Self {
        Self::LLVMBuilderError(LLVMBuilderError { fault: e })
    }
}

pub type LLVMBackendResult<T> = Result<T, LLVMBackendError>;

#[derive(Error, Debug, Diagnostic)]
#[error("LLVM builder error: {fault}")]
pub struct LLVMBuilderError {
    pub fault: BuilderError,
}
