use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_middle::hir::HirModule;
use eight_middle::mir_module::MirModule;
use eight_middle::passes::hir_lowering_pass::HirModuleLoweringPass;

/// Operation for lowering the HIR to MIR.
pub struct HirLowerPass {}

impl<'c> PipelinePass<'c, HirModule<'c>, MirModule<'c>> for HirLowerPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: HirModule<'c>,
    ) -> Result<MirModule<'c>, PipelineError> {
        let mut lowering_pass = HirModuleLoweringPass::new(&pipeline.cc);
        let module = lowering_pass.visit_module(&input)?;
        Ok(module)
    }
}
