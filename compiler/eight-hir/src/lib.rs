//! High-level Intermediate Representation.
//!
//! The High-level IR is a fully-typed, easily hackable representation of the source code. It is
//! designed to be easy to mutate and replace. It is directly derived from the syntax tree, and uses
//! the common types defined in the `ty` module for type checking and inference.
//!
//! The HIR is a concrete representation of the program (not the source code). It has all the sugar
//! and abstractions that the syntax of the language provides, providing more information about the
//! program than the AST.

use crate::item::{HirFunction, HirInstance, HirIntrinsicType, HirStruct, HirTrait};
use crate::signature::HirModuleSignature;
use std::collections::BTreeMap;

pub mod arena;
pub mod context;
pub mod error;
pub mod expr;
pub mod item;
pub mod query;
pub mod signature;
pub mod stmt;
pub mod syntax_lowering_pass;
pub mod textual_pass;
pub mod ty;
pub mod type_check_pass;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum LinkageType {
    /// The symbol is to be resolved at link-time. Typically used for symbols that are marked as
    /// intrinsic.
    External,
    /// The symbol is defined in Eight code visible to the linker.
    Eight,
}

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule<'hir> {
    pub signature: &'hir HirModuleSignature<'hir>,
    pub body: HirModuleBody<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleBody<'hir> {
    pub functions: BTreeMap<&'hir str, HirFunction<'hir>>,
    pub structs: BTreeMap<&'hir str, HirStruct<'hir>>,
    pub traits: BTreeMap<&'hir str, HirTrait<'hir>>,
    pub types: BTreeMap<&'hir str, HirIntrinsicType<'hir>>,
    pub instances: Vec<HirInstance<'hir>>,
}

impl<'hir> HirModule<'hir> {
    pub fn new(signature: &'hir HirModuleSignature<'hir>, body: HirModuleBody<'hir>) -> Self {
        Self { signature, body }
    }
}
