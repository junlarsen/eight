use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_syntax::ast::AstTranslationUnit;

/// Operation for emitting the AST.
pub struct AstEmitOperation {}
impl<'ast> PipelineOperation<'ast, AstTranslationUnit<'ast>, AstTranslationUnit<'ast>>
    for AstEmitOperation
{
    fn execute(
        pipeline: &'ast Pipeline<'ast>,
        input: AstTranslationUnit<'ast>,
    ) -> Result<AstTranslationUnit<'ast>, PipelineError> {
        if !pipeline.opts.emit_ast {
            return Ok(input);
        }
        let syntax = ron::ser::to_string_pretty(&input, Default::default())
            .expect("failed to serialize ast to ron");
        println!("{}", syntax);
        Ok(input)
    }
}
