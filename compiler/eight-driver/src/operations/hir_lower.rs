use crate::pipeline::{Pipeline, PipelineError, PipelineOperation, StopTokenStep};
use eight_middle::hir::HirModule;
use eight_middle::hir_lowering_pass::MirModuleLoweringPass;
use eight_middle::mir::MirModule;

/// Operation for lowering the HIR to MIR.
pub struct HirLowerOperation {}

impl<'c> PipelineOperation<'c, HirModule<'c>, MirModule<'c>> for HirLowerOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: HirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        if matches!(pipeline.opts.stop_token, Some(StopTokenStep::Frontend)) {
            return Err(PipelineError::StopToken("--syntax-only".to_owned()));
        }
        let mut lowering_pass = MirModuleLoweringPass::new(&pipeline.cc);
        let module = lowering_pass.visit_module(&input)?;
        Ok(module)
    }
}
