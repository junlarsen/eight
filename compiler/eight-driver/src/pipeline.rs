use crate::operations::ast_emit::AstEmitPass;
use crate::operations::ast_lower::AstLowerPass;
use crate::operations::ast_parse::AstParsePass;
use crate::operations::hir_emit::HirEmitPass;
use crate::operations::hir_lower::HirLowerPass;
use crate::operations::hir_simplify::HirSimplifyPass;
use crate::operations::hir_type_check::HirTypeCheckPass;
use crate::operations::mir_codegen_llvm::MirCodegenLLVMPass;
use crate::operations::mir_emit::MirEmitPass;
use crate::query::EmitQuery;
use eight_codegen_llvm::error::LLVMBackendError;
use eight_diagnostics::errors::hir::HirError;
use eight_diagnostics::errors::mir::MirError;
use eight_diagnostics::errors::syntax::ParseError;
use eight_diagnostics::ice;
use eight_middle::context::CompileContext;
use eight_syntax::arena::AstArena;
use miette::Diagnostic;
use std::mem::ManuallyDrop;
use thiserror::Error;

/// Execute the entire compilation pipeline.
pub fn execute_compilation_pipeline(
    opts: PipelineOptions,
    input: &str,
) -> Result<(), PipelineError> {
    let pipeline = Pipeline::new(opts);
    // Syntax passes are always ran, otherwise there's nothing for the compiler to do.
    let module = AstParsePass::execute(&pipeline, input)?;
    let module = AstEmitPass::execute(&pipeline, module)?;
    // Gate the HIR passes behind --terminator=syntax
    let module =
        pipeline.run_pass_collection_if(pipeline.is_requesting_hir(), move |pipeline| {
            let module = AstLowerPass::execute(pipeline, module)?;
            let module = HirTypeCheckPass::execute(pipeline, module)?;
            let module = HirSimplifyPass::execute(pipeline, module)?;
            let module = HirEmitPass::execute(pipeline, module)?;
            Ok(module)
        })?;
    // Gate the MIR passes behind --terminator=hir
    let module =
        pipeline.run_pass_collection_if(pipeline.is_requesting_mir(), move |pipeline| {
            let module = HirLowerPass::execute(pipeline, module)?;
            let module = MirEmitPass::execute(pipeline, module)?;
            Ok(module)
        })?;
    // Gate the Codegen passes behind --terminator=mir
    let _: () =
        pipeline.run_pass_collection_if(pipeline.is_requesting_codegen(), move |pipeline| {
            let _: () = MirCodegenLLVMPass::execute(pipeline, module)?;
            Ok(())
        })?;
    Ok(())
}

#[derive(Debug, Error, Diagnostic)]
pub enum PipelineError {
    /// Error propagated from the parser.
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseError(#[from] ParseError),

    /// Error propagated from the HIR passes.
    #[diagnostic(transparent)]
    #[error(transparent)]
    HirError(#[from] HirError),

    /// Error propagated from the MIR passes.
    #[error(transparent)]
    #[diagnostic(transparent)]
    MirError(#[from] MirError),

    /// Error propagated from the LLVM backend.
    #[error(transparent)]
    #[diagnostic(transparent)]
    LLVMBackendError(#[from] LLVMBackendError),

    /// Stop token to abort the compilation pipeline.
    #[error("compilation flags caused early termination: {0}")]
    StopToken(String),
}

/// Stop token indicating that the pipeline should stop after a certain step.
#[derive(Eq, PartialEq)]
pub enum TerminationStep {
    Syntax,
    Hir,
    Mir,
}

/// Options for the compilation pipeline.
///
/// Most of these are derived from the command line arguments.
pub struct PipelineOptions {
    pub emit_ast: bool,
    pub emit_hir: bool,
    pub emit_mir: bool,
    pub termination_step: Option<TerminationStep>,
    pub queries: Vec<EmitQuery>,
}

/// A compilation pipeline for the compiler.
pub struct Pipeline<'c> {
    pub(crate) opts: PipelineOptions,
    pub(crate) cc: ManuallyDrop<CompileContext<'c>>,
    pub(crate) ast_arena: ManuallyDrop<AstArena<'c>>,
}

impl<'c> Pipeline<'c> {
    pub fn new(opts: PipelineOptions) -> Self {
        Self {
            opts,
            cc: ManuallyDrop::new(CompileContext::new()),
            ast_arena: ManuallyDrop::new(AstArena::default()),
        }
    }

    /// Codegen passes run if the stop token is not set to MIR.
    pub fn is_requesting_codegen(&self) -> bool {
        !matches!(
            self.opts.termination_step,
            Some(TerminationStep::Mir | TerminationStep::Hir | TerminationStep::Syntax)
        )
    }

    /// MIR passes run if the stop token is not set to HIR.
    pub fn is_requesting_mir(&self) -> bool {
        !matches!(
            self.opts.termination_step,
            Some(TerminationStep::Hir | TerminationStep::Syntax)
        )
    }

    /// HIR passes run if the stop token is not set to Syntax.
    pub fn is_requesting_hir(&self) -> bool {
        !matches!(self.opts.termination_step, Some(TerminationStep::Syntax))
    }

    /// Get the error to return if the pipeline is early terminated.
    pub fn get_terminator_error(&self) -> PipelineError {
        match self.opts.termination_step {
            Some(TerminationStep::Syntax) => {
                PipelineError::StopToken("--terminator=syntax".to_owned())
            }
            Some(TerminationStep::Mir) => PipelineError::StopToken("--terminator=mir".to_owned()),
            Some(TerminationStep::Hir) => PipelineError::StopToken("--terminator=hir".to_owned()),
            None => ice!("called get_terminator_error() when no early termination was requested"),
        }
    }

    /// Run the `operation` if `cond` is true.
    ///
    /// This is used for grouping passes under conditions. This can for example, disable codegen if
    /// compiler arguments specify to not run the backend.
    pub fn run_pass_collection_if<O>(
        &'c self,
        cond: bool,
        operation: impl FnOnce(&'c Pipeline<'c>) -> Result<O, PipelineError>,
    ) -> Result<O, PipelineError> {
        if cond {
            operation(self)
        } else {
            Err(self.get_terminator_error())
        }
    }
}

/// Trait for executing an operation in the pipeline.
pub trait PipelinePass<'c, I, O> {
    /// Execute the operation.
    ///
    /// The implementation itself should determine if it should run or not.
    ///
    /// Optional passes should have I be equal to O.
    fn execute(pipeline: &'c Pipeline<'c>, input: I) -> Result<O, PipelineError>;
}
