use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_hir::syntax_lowering_pass::AstSyntaxLoweringPass;
use eight_middle::hir::module::HirModule;
use eight_syntax::ast::AstTranslationUnit;

/// Operation for lowering the AST to HIR.
pub struct SyntaxLowerOperation {}
impl<'c> PipelineOperation<'c, AstTranslationUnit<'c>, HirModule<'c>> for SyntaxLowerOperation {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: AstTranslationUnit<'c>,
    ) -> Result<HirModule<'c>, PipelineError> {
        let mut lowering_pass = AstSyntaxLoweringPass::new(&pipeline.hir_arena);
        let module = lowering_pass.visit_translation_unit(&input)?;
        Ok(module)
    }
}
