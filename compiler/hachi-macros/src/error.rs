//! Module for declaring compiler diagnostic error types.
//!
//! This module exports a macro [`declare_error_type`] that can be used to define a new error that
//! the compiler infrastructure can use as a diagnostic error.

/// Declare a new error type that can be used as a diagnostic error.
#[macro_export]
macro_rules! declare_error_type {
    {
        #[error($msg:expr)]
        $vis:vis enum $type_name:ident {
            $($name:ident($ty:ty),)*
        }
    } => {
        #[derive(thiserror::Error, miette::Diagnostic, Debug)]
        #[error($msg)]
        $vis enum $type_name {
            $(
                #[error(transparent)]
                #[diagnostic(transparent)]
                $name(#[from] $ty),
            )*
        }
    }
}
