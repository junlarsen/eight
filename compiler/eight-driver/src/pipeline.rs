use crate::query::EmitQuery;
use eight_diagnostics::ice;
use eight_hir::arena::HirArena;
use eight_hir::error::HirError;
use eight_hir::query::HirQueryDatabase;
use eight_hir::syntax_lowering_pass::AstSyntaxLoweringPass;
use eight_hir::textual_pass::HirModuleTextualPass;
use eight_hir::type_check_pass::{HirModuleTypeCheckerPass, TypingContext};
use eight_hir::HirModule;
use eight_syntax::arena::AstArena;
use eight_syntax::ast::AstTranslationUnit;
use eight_syntax::error::ParseError;
use eight_syntax::lexer::Lexer;
use eight_syntax::parser::Parser;
use miette::Diagnostic;
use std::cell::OnceCell;
use std::mem::ManuallyDrop;
use thiserror::Error;

/// Execute the entire compilation pipeline.
pub fn execute_compilation_pipeline(
    opts: PipelineOptions,
    input: &str,
) -> Result<(), PipelineError> {
    let pipeline = Pipeline::new(opts);
    let tu = ParseOperation::execute(&pipeline, input)?;
    let tu = AstEmitOperation::execute(&pipeline, tu)?;
    let module = SyntaxLowerOperation::execute(&pipeline, tu)?;
    let module = TypeCheckOperation::execute(&pipeline, module)?;
    let _ = HirEmitOperation::execute(&pipeline, module)?;
    Ok(())
}

#[derive(Debug, Error, Diagnostic)]
pub enum PipelineError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    LexerError(#[from] ParseError),
    #[diagnostic(transparent)]
    #[error(transparent)]
    HirError(#[from] HirError),
}

/// Options for the compilation pipeline.
///
/// Most of these are derived from the command line arguments.
pub struct PipelineOptions {
    pub emit_ast: bool,
    pub emit_hir: bool,
    pub queries: Vec<EmitQuery>,
}

/// A compilation pipeline for the compiler.
pub struct Pipeline<'c> {
    opts: PipelineOptions,
    ast_arena: ManuallyDrop<AstArena<'c>>,
    hir_arena: ManuallyDrop<HirArena<'c>>,
    hir_query_database: OnceCell<HirQueryDatabase<'c>>,
}

impl<'c> Pipeline<'c> {
    pub fn new(opts: PipelineOptions) -> Self {
        Self {
            opts,
            ast_arena: ManuallyDrop::new(AstArena::default()),
            hir_arena: ManuallyDrop::new(HirArena::default()),
            hir_query_database: OnceCell::new(),
        }
    }
}

/// Enum describing how crucial a pass in the pipeline is.
pub enum PipelineRequirement {
    Required,
    Optional,
}

pub trait PipelineOperation<'c, I, O> {
    fn execute(pipeline: &'c Pipeline<'c>, input: I) -> Result<O, PipelineError>;
}

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

/// Operation for type checking the HIR.
pub struct TypeCheckOperation {}
impl<'hir> PipelineOperation<'hir, HirModule<'hir>, HirModule<'hir>> for TypeCheckOperation {
    fn execute(
        pipeline: &'hir Pipeline<'hir>,
        mut input: HirModule<'hir>,
    ) -> Result<HirModule<'hir>, PipelineError> {
        let query_database = HirQueryDatabase::new(input.signature);
        pipeline
            .hir_query_database
            .set(query_database)
            .unwrap_or_else(|_| {
                ice!("failed to assign OnceCell for query database");
            });

        let mut typing_context = TypingContext::new(
            &pipeline.hir_arena,
            pipeline
                .hir_query_database
                .get()
                .unwrap_or_else(|| ice!("failed to get query database")),
        );
        HirModuleTypeCheckerPass::visit(&mut input, &mut typing_context)?;
        Ok(input)
    }
}

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

/// Operation for emitting the HIR.
pub struct HirEmitOperation;
impl<'hir> PipelineOperation<'hir, HirModule<'hir>, HirModule<'hir>> for HirEmitOperation {
    fn execute(
        pipeline: &'hir Pipeline<'hir>,
        input: HirModule<'hir>,
    ) -> Result<HirModule<'hir>, PipelineError> {
        if !pipeline.opts.emit_hir {
            return Ok(input);
        }
        let textual_pass = HirModuleTextualPass::default();
        let doc = textual_pass.visit_module(&input);
        let document = HirModuleTextualPass::format_doc_to_string(doc);
        println!("{}", document);
        Ok(input)
    }
}
