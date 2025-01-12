use crate::pipeline::{Pipeline, PipelineError, PipelineOperation};
use eight_syntax::ast::AstTranslationUnit;
use eight_syntax::lexer::Lexer;
use eight_syntax::parser::Parser;

/// Operation for parsing the input source into an AST.
pub struct ParseOperation {}
impl<'ast, T: AsRef<str>> PipelineOperation<'ast, T, AstTranslationUnit<'ast>> for ParseOperation {
    fn execute(
        pipeline: &'ast Pipeline<'ast>,
        input: T,
    ) -> Result<AstTranslationUnit<'ast>, PipelineError> {
        let mut lexer = Lexer::new(input.as_ref());
        let mut parser = Parser::new(&mut lexer, &pipeline.ast_arena);
        let translation_unit = parser.parse()?;
        Ok(translation_unit)
    }
}
