use hachi_macros::declare_error_type;
use hachi_syntax::Span;
use miette::Diagnostic;
use thiserror::Error;

declare_error_type! {
    #[error("parser error: {0}")]
    pub enum TypeError {
        InvalidTypeReference(InvalidTypeReferenceError),
        InvalidValueReference(InvalidValueReferenceError),
        ReturnOutsideOfFunction(ReturnOutsideOfFunctionError),
        ValueReturnFromVoidFunction(ValueReturnFromVoidFunctionError),
        VoidReturnFromNonVoidFunction(VoidReturnFromNonVoidFunctionError),
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

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::return_outside_of_function))]
#[error("attempted to return from outside of a function")]
pub struct ReturnOutsideOfFunctionError {
    #[label = "attempted to return from outside of a function"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::value_return_from_void_function))]
#[error("attempted to return a value from a void function")]
pub struct ValueReturnFromVoidFunctionError {
    #[label = "the function is annotated to return void"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::void_return_from_non_void_function))]
#[error("attempted to return a value from a non-void function")]
pub struct VoidReturnFromNonVoidFunctionError {
    #[label = "the function is not annotated to return void"]
    pub span: Span,
}
