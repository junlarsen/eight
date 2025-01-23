use crate::pipeline::{PipelineOperation, StopTokenStep};
use eight_codegen_llvm::{LLVMCodeGeneratorContext, MirModuleLLVMCodeGeneratorPass};
use eight_middle::mir::MirModule;

/// Operation for generating LLVM IR from the MIR.
pub struct CodegenLLVMOperation {}
impl<'c> PipelineOperation<'c, MirModule<'c>, ()> for CodegenLLVMOperation {
    fn execute(
        pipeline: &'c crate::pipeline::Pipeline<'c>,
        input: MirModule<'c>,
    ) -> Result<(), crate::pipeline::PipelineError> {
        if matches!(pipeline.opts.stop_token, Some(StopTokenStep::Middle)) {
            return Err(crate::pipeline::PipelineError::StopToken(
                "--mir-only".to_owned(),
            ));
        }
        let codegen_context = LLVMCodeGeneratorContext::new();
        let mut pass = MirModuleLLVMCodeGeneratorPass::new(&codegen_context);
        pass.visit_module(&input)?;
        pass.finish();
        Ok(())
    }
}
