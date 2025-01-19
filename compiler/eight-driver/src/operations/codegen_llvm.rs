use crate::pipeline::PipelineOperation;
use eight_codegen_llvm::{LLVMCodeGeneratorContext, MirModuleLLVMCodeGeneratorPass};
use eight_middle::mir::module::MirModule;

/// Operation for generating LLVM IR from the MIR.
pub struct CodegenLLVMOperation {}
impl<'c> PipelineOperation<'c, MirModule<'c>, ()> for CodegenLLVMOperation {
    fn execute(
        _: &'c crate::pipeline::Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<(), crate::pipeline::PipelineError> {
        let codegen_context = LLVMCodeGeneratorContext::new();
        let mut pass = MirModuleLLVMCodeGeneratorPass::new(&codegen_context);
        pass.visit_module(&input);
        pass.finish();
        Ok(())
    }
}
