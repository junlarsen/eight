//! Common types and functions for the middle-end of the compiler.

pub mod ast_lowering_pass;
pub mod builtin;
pub mod context;
pub mod hir;
pub mod hir_builder;
pub mod hir_error;
pub mod hir_lowering_pass;
pub mod hir_query;
pub mod hir_textual_pass;
pub mod hir_type_check_pass;
pub mod intern;
pub mod mir;
pub mod mir_builder;
pub mod mir_error;
pub mod mir_textual_pass;
pub mod scope;

#[derive(Debug, PartialEq, Eq)]
pub enum LinkageType {
    /// The symbol is to be resolved at link-time. Typically used for symbols that are marked as
    /// intrinsic.
    External,
    /// The symbol is defined in Eight code visible to the linker.
    Eight,
}
