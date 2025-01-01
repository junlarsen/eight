use hachi_macros::declare_error_type;
use hachi_syntax::Span;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("syntax lowering error: {0}")]
    pub enum SyntaxLoweringError {
        BreakOutsideLoop(BreakOutsideLoopError),
        ContinueOutsideLoop(ContinueOutsideLoopError),
    }
}

/// Handy type alias for all HIR-related errors.
pub type SyntaxLoweringResult<T> = Result<T, SyntaxLoweringError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::break_outside_loop))]
#[error("break statement outside of loop")]
pub struct BreakOutsideLoopError {
    #[label = "there is no enclosing loop"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::continue_outside_loop))]
#[error("continue statement outside of loop")]
pub struct ContinueOutsideLoopError {
    #[label = "there is no enclosing loop"]
    pub span: Span,
}
