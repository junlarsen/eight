use crate::operations::emit_ast::AstEmitOperation;
use crate::operations::emit_hir::HirEmitOperation;
use crate::operations::parse::ParseOperation;
use crate::operations::syntax_lower::SyntaxLowerOperation;
use crate::operations::type_check::TypeCheckOperation;
use crate::query::EmitQuery;
use eight_diagnostics::ice;
use eight_hir::arena::HirArena;
use eight_hir::error::HirError;
use eight_hir::query::HirSignatureQueryDatabase;
use eight_syntax::arena::AstArena;
use eight_syntax::error::ParseError;
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
    pub(crate) opts: PipelineOptions,
    pub(crate) ast_arena: ManuallyDrop<AstArena<'c>>,
    pub(crate) hir_arena: ManuallyDrop<HirArena<'c>>,
    pub(crate) hir_query_database: OnceCell<HirSignatureQueryDatabase<'c>>,
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

    /// Get the HIR query database.
    pub fn query_database(&self) -> &HirSignatureQueryDatabase {
        self.hir_query_database.get().unwrap_or_else(|| {
            ice!("failed to get query database, are you sure the hir lowering has been executed?")
        })
    }
}

/// Enum describing how crucial a pass in the pipeline is.
pub enum PipelineRequirement {
    Required,
    Optional,
}

/// Trait for executing an operation in the pipeline.
pub trait PipelineOperation<'c, I, O> {
    /// Execute the operation.
    ///
    /// The implementation itself should determine if it should run or not.
    ///
    /// Optional passes should have I be equal to O.
    fn execute(pipeline: &'c Pipeline<'c>, input: I) -> Result<O, PipelineError>;
}
