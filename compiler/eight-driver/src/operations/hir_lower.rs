use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_middle::hir::HirModule;
use eight_middle::hir_lowering_pass::MirModuleLoweringPass;
use eight_middle::mir::MirModule;

/// Operation for lowering the HIR to MIR.
pub struct HirLowerPass {}

impl<'c> PipelinePass<'c, HirModule<'c>, MirModule<'c>> for HirLowerPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: HirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        let mut lowering_pass = MirModuleLoweringPass::new(&pipeline.cc);
        let module = lowering_pass.visit_module(&input)?;
        Ok(module)
    }
}
