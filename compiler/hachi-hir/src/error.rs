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
    }
}

/// Handy type alias for all HIR-related errors.
pub type HirResult<T> = Result<T, HirError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(semantic::unknown_type))]
#[error("{name} does not name a known type")]
pub struct UnknownTypeError {
    pub name: String,
    #[label = "could not find type {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(semantic::invalid_reference))]
#[error("invalid reference to {name}")]
pub struct InvalidReferenceError {
    pub name: String,
    #[label = "could not find value named {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(semantic::infinitely_recursive_type))]
#[error("type is recursive")]
pub struct TypeFieldInfiniteRecursionError {
    pub type_name: String,
    pub offending_field: String,
    #[label = "type {type_name} has an infinite recursion in field {offending_field}"]
    pub span: Span,
}
