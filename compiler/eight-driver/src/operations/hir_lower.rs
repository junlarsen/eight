use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_middle::hir::module::HirModule;
use eight_middle::mir::module::MirModule;
use eight_mir::hir_lowering_pass::MirModuleLoweringPass;

/// Operation for lowering the HIR to MIR.
pub struct HirLowerOperation {}

impl<'c> PipelineOperation<'c, HirModule<'c>, MirModule<'c>> for HirLowerOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: HirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        if pipeline.opts.syntax_only {
            return Err(PipelineError::StopToken("--syntax-only".to_owned()));
        }

        let mut lowering_pass = MirModuleLoweringPass::new(&pipeline.cc);
        let module = lowering_pass.visit_module(&input)?;
        Ok(module)
    }
}
