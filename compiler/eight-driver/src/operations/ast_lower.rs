use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_middle::hir::HirModule;
use eight_middle::passes::ast_lowering_pass::AstLoweringPass;
use eight_syntax::ast::AstTranslationUnit;

/// Operation for lowering the AST to HIR.
pub struct AstLowerPass {}
impl<'c> PipelinePass<'c, AstTranslationUnit<'c>, HirModule<'c>> for AstLowerPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: AstTranslationUnit<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let mut lowering_pass = AstLoweringPass::new(&pipeline.cc);
        let module = lowering_pass.visit_translation_unit(&input)?;
        Ok(module)
    }
}
