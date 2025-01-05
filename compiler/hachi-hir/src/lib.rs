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
use crate::scalar::HirIntrinsicScalar;
use crate::ty::HirTyArena;
use hachi_span::Span;
use std::collections::BTreeMap;

pub mod context;
pub mod error;
pub mod expr;
pub mod fun;
pub mod passes;
pub mod rec;
pub mod scalar;
pub mod stmt;
pub mod ty;

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule<'ta> {
    pub intrinsic_scalars: BTreeMap<String, HirIntrinsicScalar<'ta>>,
    pub records: BTreeMap<String, HirRecord<'ta>>,
    pub functions: BTreeMap<String, HirFunction<'ta>>,
    pub intrinsic_functions: BTreeMap<String, HirIntrinsicFunction<'ta>>,
}

impl<'ta> HirModule<'ta> {
    /// Create an empty Hir module.
    pub fn new(arena: &'ta HirTyArena<'ta>) -> Self {
        Self {
            records: BTreeMap::new(),
            functions: BTreeMap::new(),
            intrinsic_functions: BTreeMap::new(),
            intrinsic_scalars: BTreeMap::from([
                (
                    "i32".to_owned(),
                    HirIntrinsicScalar {
                        name: "i32".to_owned(),
                        ty: arena.get_integer32_ty(),
                    },
                ),
                (
                    "bool".to_owned(),
                    HirIntrinsicScalar {
                        name: "bool".to_owned(),
                        ty: arena.get_boolean_ty(),
                    },
                ),
                (
                    "unit".to_owned(),
                    HirIntrinsicScalar {
                        name: "unit".to_owned(),
                        ty: arena.get_unit_ty(),
                    },
                ),
            ]),
        }
    }

    /// Get a record type from the module with the given name.
    pub fn get_record_type(&self, name: &str) -> Option<&HirRecord> {
        self.records.get(name)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirName {
    pub name: String,
    pub span: Span,
}
