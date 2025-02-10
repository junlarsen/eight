use crate::pipeline::{Pipeline, PipelineError, PipelinePass};
use eight_syntax::ast::AstTranslationUnit;
use eight_syntax::lexer::Lexer;
use eight_syntax::parser::Parser;

/// Operation for parsing the input source into an AST.
pub struct AstParsePass {}
impl<'c, T: AsRef<str>> PipelinePass<'c, T, AstTranslationUnit<'c>> for AstParsePass {
    fn execute(
        pipeline: &'c Pipeline<'c>,
        input: T,
    ) -> Result<AstTranslationUnit<'c>, PipelineError> {
        let mut lexer = Lexer::new(input.as_ref(), pipeline.dcx());
        let mut parser = Parser::new(&mut lexer, &pipeline.ast_arena, pipeline.dcx());
        let translation_unit = parser.parse()?;
        Ok(translation_unit)
    }
}
