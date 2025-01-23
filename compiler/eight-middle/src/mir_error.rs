use eight_macros::declare_error_type;

declare_error_type! {
    #[error("mir lowering error: {0}")]
    pub enum MirError {
    }
}

pub type MirResult<T> = Result<T, MirError>;
