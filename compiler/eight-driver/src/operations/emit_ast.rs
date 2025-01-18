use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_syntax::ast::AstTranslationUnit;

/// Operation for emitting the AST.
pub struct AstEmitOperation {}
impl<'c> PipelineOperation<'c, AstTranslationUnit<'c>, AstTranslationUnit<'c>>
    for AstEmitOperation
{
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
