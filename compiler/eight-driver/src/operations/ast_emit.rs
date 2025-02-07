use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_syntax::ast::AstTranslationUnit;

/// Operation for emitting the AST.
pub struct AstEmitPass {}
impl<'c> PipelinePass<'c, AstTranslationUnit<'c>, AstTranslationUnit<'c>> for AstEmitPass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: AstTranslationUnit<'c>,
    ) -> Result<AstTranslationUnit<'c>, PipelineError> {
        if !pipeline.opts.emit_ast {
            return Ok(input);
        }
        let syntax = ron::ser::to_string_pretty(&input, Default::default())
            .expect("failed to serialize ast to ron");
        println!("{}", syntax);
        Ok(input)
    }
}
