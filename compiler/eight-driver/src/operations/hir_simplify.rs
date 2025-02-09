use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_middle::hir::HirModule;

/// Operation for type guided simplification of the HIR.
pub struct HirSimplifyPass {}

impl<'c> PipelinePass<'c, HirModule<'c>, HirModule<'c>> for HirSimplifyPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        mut input: HirModule<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let mut lowering_pass =
            eight_middle::passes::hir_simplify_pass::HirSimplifyPass::new(pipeline.session);
        lowering_pass.visit_module(&mut input);
        Ok(input)
    }
}
