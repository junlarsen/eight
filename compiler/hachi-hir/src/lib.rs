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
use crate::ty::HirTy;
use hachi_syntax::Span;
use std::collections::HashMap;

mod error;
mod expr;
mod fun;
mod passes;
mod stmt;
mod ty;

pub type HirId = usize;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirModule<'hir> {
    pub types: HashMap<&'hir str, HirTy<'hir>>,
    pub functions: HashMap<&'hir str, HirFun<'hir>>,
}

impl<'hir> HirModule<'hir> {
    pub fn new() -> Self {
        Self {
            types: HashMap::new(),
            functions: HashMap::new(),
        }
    }
}

impl<'hir> Default for HirModule<'hir> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirName<'hir> {
    pub name: String,
    pub span: Span,
}
