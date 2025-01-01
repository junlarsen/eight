use hachi_macros::declare_error_type;

declare_error_type! {
    #[error("parser error: {0}")]
    pub enum HirError {
    }
}

/// Handy type alias for all HIR-related errors.
pub type HirResult<T> = Result<T, HirError>;
