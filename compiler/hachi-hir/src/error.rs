use hachi_macros::declare_error_type;
use hachi_syntax::Span;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("semantic error: {0}")]
    pub enum HirError {
        UnknownType(UnknownTypeError),
        InvalidReference(InvalidReferenceError),
        TypeFieldInfiniteRecursion(TypeFieldInfiniteRecursionError),
        BreakOutsideLoop(BreakOutsideLoopError),
        ContinueOutsideLoop(ContinueOutsideLoopError),
    }
}

/// Handy type alias for all HIR-related errors.
pub type HirResult<T> = Result<T, HirError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::unknown_type))]
#[error("{name} does not name a known type")]
pub struct UnknownTypeError {
    pub name: String,
    #[label = "could not find type {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_reference))]
#[error("invalid reference to {name}")]
pub struct InvalidReferenceError {
    pub name: String,
    #[label = "could not find value named {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::infinitely_recursive_type))]
#[error("type is recursive")]
pub struct TypeFieldInfiniteRecursionError {
    pub type_name: String,
    pub offending_field: String,
    #[label = "type {type_name} has an infinite recursion in field {offending_field}"]
    pub span: Span,
}

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
