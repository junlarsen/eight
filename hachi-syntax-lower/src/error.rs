use hachi_macros::declare_error_type;
use hachi_syntax::Span;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("parser error: {0}")]
    pub enum TypeError {
        InvalidTypeReference(InvalidTypeReferenceError),
        InvalidValueReference(InvalidValueReferenceError),
    }
}

pub type TypeResult<T> = Result<T, TypeError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_type_reference))]
#[error("attempted to reference a type named {name} that does not exist")]
pub struct InvalidTypeReferenceError {
    #[label = "the type {name} does not exist"]
    pub span: Span,
    pub name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_value_reference))]
#[error("attempted to reference a value named {name} that does not exist")]
pub struct InvalidValueReferenceError {
    #[label = "the value {name} does not exist"]
    pub span: Span,
    pub name: String,
}
