use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_hir::syntax_lowering_pass::AstSyntaxLoweringPass;
use eight_hir::HirModule;
use eight_syntax::ast::AstTranslationUnit;

/// Operation for lowering the AST to HIR.
pub struct SyntaxLowerOperation {}
impl<'hir> PipelineOperation<'hir, AstTranslationUnit<'hir>, HirModule<'hir>>
    for SyntaxLowerOperation
{
    fn execute(
        pipeline: &'hir Pipeline<'hir>,
        input: AstTranslationUnit<'hir>,
    ) -> Result<HirModule<'hir>, PipelineError> {
        let lowering_pass = AstSyntaxLoweringPass::new(&pipeline.hir_arena);
        let module = lowering_pass.visit_translation_unit(&input)?;
        Ok(module)
    }
}
