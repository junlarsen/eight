//! High-level Intermediate Representation.
//!
//! The High-level IR is a fully-typed, easily hackable representation of the source code. It is
//! designed to be easy to mutate and replace. It is directly derived from the syntax tree, and uses
//! the common types defined in the `ty` module for type checking and inference.
//!
//! The HIR is a concrete representation of the program (not the source code). It has all the sugar
//! and abstractions that the syntax of the language provides, providing more information about the
//! program than the AST.

use crate::item::{
    HirFunction, HirInstance, HirIntrinsicFunction, HirIntrinsicScalar, HirRecord, HirTrait,
};
use crate::signature::HirModuleSignature;
use eight_span::Span;
use std::cell::RefCell;
use std::collections::BTreeMap;

pub mod arena;
pub mod context;
pub mod error;
pub mod expr;
pub mod item;
pub mod passes;
pub mod signature;
pub mod stmt;
pub mod ty;

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule<'ta> {
    pub signature: RefCell<HirModuleSignature<'ta>>,
    pub intrinsic_scalars: BTreeMap<String, HirIntrinsicScalar<'ta>>,
    pub records: BTreeMap<String, HirRecord<'ta>>,
    pub functions: BTreeMap<String, HirFunction<'ta>>,
    pub intrinsic_functions: BTreeMap<String, HirIntrinsicFunction<'ta>>,
    pub traits: BTreeMap<String, HirTrait<'ta>>,
    pub instances: BTreeMap<String, Vec<HirInstance<'ta>>>,
}

impl<'ta> Default for HirModule<'ta> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'ta> HirModule<'ta> {
    /// Create an empty Hir module.
    pub fn new() -> Self {
        Self {
            signature: RefCell::new(HirModuleSignature::default()),
            records: BTreeMap::new(),
            functions: BTreeMap::new(),
            intrinsic_functions: BTreeMap::new(),
            intrinsic_scalars: BTreeMap::new(),
            traits: BTreeMap::new(),
            instances: BTreeMap::new(),
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
