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
use crate::ty::{HirBooleanTy, HirInteger32Ty, HirTy, HirUnitTy};
use hachi_span::Span;
use std::collections::BTreeMap;
use std::marker::PhantomData;

pub mod context;
pub mod error;
pub mod expr;
pub mod format;
pub mod fun;
pub mod passes;
pub mod rec;
pub mod stmt;
pub mod syntax_lowering;
pub mod ty;

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule<'hir> {
    pub scalars: BTreeMap<String, HirTy>,
    pub records: BTreeMap<String, HirRecord>,
    pub functions: BTreeMap<String, HirFun>,
    phantom: PhantomData<&'hir ()>,
}

impl<'hir> HirModule<'hir> {
    /// Create an empty Hir module.
    pub fn new() -> Self {
        Self {
            records: BTreeMap::new(),
            functions: BTreeMap::new(),
            scalars: BTreeMap::from([
                (
                    "i32".to_owned(),
                    HirTy::Integer32(HirInteger32Ty {
                        span: Span::empty(),
                    }),
                ),
                (
                    "bool".to_owned(),
                    HirTy::Boolean(HirBooleanTy {
                        span: Span::empty(),
                    }),
                ),
                (
                    "unit".to_owned(),
                    HirTy::Unit(HirUnitTy {
                        span: Span::empty(),
                    }),
                ),
            ]),
            phantom: PhantomData,
        }
    }

    /// Get the named function from the module with the given name.
    pub fn get_function(&'hir self, name: &str) -> Option<&'hir HirFun> {
        self.functions.get(name)
    }

    /// Get the named type from the module with the given name.
    pub fn get_scalar_type(&'hir self, name: &str) -> Option<&'hir HirTy> {
        self.scalars.get(name)
    }

    /// Get the builtin integer32 type.
    pub fn get_builtin_integer32_type(&'hir self) -> &'hir HirTy {
        self.scalars
            .get("i32")
            .expect("builtin integer32 type not found")
    }

    /// Get the builtin boolean type.
    pub fn get_builtin_boolean_type(&'hir self) -> &'hir HirTy {
        self.scalars
            .get("bool")
            .expect("builtin boolean type not found")
    }

    /// Get the builtin unit type.
    pub fn get_builtin_unit_type(&'hir self) -> &'hir HirTy {
        self.scalars
            .get("unit")
            .expect("builtin unit type not found")
    }

    /// Get a record type from the module with the given name.
    pub fn get_record_type(&'hir self, name: &str) -> Option<&'hir HirRecord> {
        self.records.get(name)
    }
}

impl<'hir> Default for HirModule<'hir> {
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
