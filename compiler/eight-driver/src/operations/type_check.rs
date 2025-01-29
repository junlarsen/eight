use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_middle::hir::HirModule;
use eight_middle::hir_type_check_pass::{HirModuleTypeCheckerPass, TypingContext};

/// Operation for type checking the HIR.
pub struct TypeCheckOperation {}
impl<'c> PipelineOperation<'c, HirModule<'c>, HirModule<'c>> for TypeCheckOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        mut input: HirModule<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let mut typing_context = TypingContext::new(&pipeline.cc, input.signature);
        HirModuleTypeCheckerPass::visit(&mut input, &mut typing_context)?;
        Ok(input)
    }
}
