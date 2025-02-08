use crate::pipeline::PipelinePass;
use eight_codegen_llvm::{LLVMCodeGeneratorContext, MirModuleLLVMCodeGeneratorPass};
use eight_middle::mir_module::MirModule;

/// Operation for generating LLVM IR from the MIR.
pub struct MirCodegenLLVMPass {}
impl<'c> PipelinePass<'c, MirModule<'c>, ()> for MirCodegenLLVMPass {
    fn execute(
        _: &'c crate::pipeline::Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<(), crate::pipeline::PipelineError> {
        let codegen_context = LLVMCodeGeneratorContext::new();
        let mut pass = MirModuleLLVMCodeGeneratorPass::new(&codegen_context);
        pass.visit_module(&input)?;
        pass.finish();
        Ok(())
    }
}
