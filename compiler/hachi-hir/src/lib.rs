//! High-level Intermediate Representation.
//!
//! The High-level IR is a fully-typed, easily hackable representation of the source code. It is
//! designed to be easy to mutate and replace. It is directly derived from the syntax tree, and uses
//! the common types defined in the `ty` module for type checking and inference.
//!
//! The HIR is a concrete representation of the program (not the source code). It has all the sugar
//! and abstractions that the syntax of the language provides, providing more information about the
//! program than the AST.

use crate::fun::HirFun;
use crate::rec::HirRecord;
use hachi_syntax::Span;
use std::collections::BTreeMap;

pub mod context;
pub mod error;
pub mod expr;
pub mod format;
pub mod fun;
pub mod passes;
mod rec;
pub mod stmt;
pub mod syntax_lowering;
pub mod ty;

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule {
    pub records: BTreeMap<String, HirRecord>,
    pub functions: BTreeMap<String, HirFun>,
}

impl HirModule {
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
            functions: BTreeMap::new(),
        }
    }
}

impl Default for HirModule {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirName {
    pub name: String,
    pub span: Span,
}
