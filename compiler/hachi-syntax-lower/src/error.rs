use hachi_macros::declare_error_type;

declare_error_type! {
    #[error("syntax lowering error: {0}")]
    pub enum SyntaxLoweringError {

    }
}

/// Handy type alias for all HIR-related errors.
pub type SyntaxLoweringResult<T> = Result<T, SyntaxLoweringError>;
