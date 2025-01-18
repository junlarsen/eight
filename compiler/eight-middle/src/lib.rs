//! Common types and functions for the middle-end of the compiler.

pub mod arena;
pub mod context;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum LinkageType {
    /// The symbol is to be resolved at link-time. Typically used for symbols that are marked as
    /// intrinsic.
    External,
    /// The symbol is defined in Eight code visible to the linker.
    Eight,
}
