use crate::Span;
use miette::Diagnostic;
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
#[error("unexpectedly reached the end of the input source")]
#[diagnostic(code(E0001))]
pub struct UnexpectedEndOfInput {
    #[label("expected more characters after this")]
    pub span: Span,
}
