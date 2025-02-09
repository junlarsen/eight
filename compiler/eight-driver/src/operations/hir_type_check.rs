use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_middle::hir::HirModule;
use eight_middle::passes::hir_type_check_pass::{HirModuleTypeCheckerPass, TypingContext};

/// Operation for type checking the HIR.
pub struct HirTypeCheckPass {}
impl<'c> PipelinePass<'c, HirModule<'c>, HirModule<'c>> for HirTypeCheckPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        mut input: HirModule<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let mut typing_context = TypingContext::new(pipeline.session, input.signature);
        HirModuleTypeCheckerPass::visit(&mut input, &mut typing_context)?;
        Ok(input)
    }
}
