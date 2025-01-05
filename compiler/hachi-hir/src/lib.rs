//! High-level Intermediate Representation.
//!
//! The High-level IR is a fully-typed, easily hackable representation of the source code. It is
//! designed to be easy to mutate and replace. It is directly derived from the syntax tree, and uses
//! the common types defined in the `ty` module for type checking and inference.
//!
//! The HIR is a concrete representation of the program (not the source code). It has all the sugar
//! and abstractions that the syntax of the language provides, providing more information about the
//! program than the AST.

use crate::fun::{HirFunction, HirIntrinsicFunction};
use crate::rec::HirRecord;
use crate::ty::{HirBooleanTy, HirInteger32Ty, HirTy, HirUnitTy};
use hachi_diagnostics::ice;
use hachi_span::Span;
use std::collections::BTreeMap;

pub mod context;
pub mod error;
pub mod expr;
pub mod fun;
pub mod passes;
pub mod rec;
pub mod stmt;
pub mod ty;

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule {
    pub intrinsic_scalars: BTreeMap<String, HirTy>,
    pub records: BTreeMap<String, HirRecord>,
    pub functions: BTreeMap<String, HirFunction>,
    pub intrinsic_functions: BTreeMap<String, HirIntrinsicFunction>,
}

impl HirModule {
    /// Create an empty Hir module.
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
            functions: BTreeMap::new(),
            intrinsic_functions: BTreeMap::new(),
            intrinsic_scalars: BTreeMap::from([
                ("i32".to_owned(), HirTy::Integer32(HirInteger32Ty {})),
                ("bool".to_owned(), HirTy::Boolean(HirBooleanTy {})),
                ("unit".to_owned(), HirTy::Unit(HirUnitTy {})),
            ]),
        }
    }

    /// Get the builtin integer32 type.
    pub fn get_builtin_integer32_type(&self) -> &HirTy {
        self.intrinsic_scalars
            .get("i32")
            .unwrap_or_else(|| ice!("builtin integer32 type not found"))
    }

    /// Get the builtin boolean type.
    pub fn get_builtin_boolean_type(&self) -> &HirTy {
        self.intrinsic_scalars
            .get("bool")
            .unwrap_or_else(|| ice!("builtin boolean type not found"))
    }

    /// Get the builtin unit type.
    pub fn get_builtin_unit_type(&self) -> &HirTy {
        self.intrinsic_scalars
            .get("unit")
            .unwrap_or_else(|| ice!("builtin unit type not found"))
    }

    /// Get a record type from the module with the given name.
    pub fn get_record_type(&self, name: &str) -> Option<&HirRecord> {
        self.records.get(name)
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
