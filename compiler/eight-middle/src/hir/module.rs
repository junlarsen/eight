use crate::hir::item::{HirFunction, HirInstance, HirStruct, HirTrait, HirType};
use crate::hir::signature::HirModuleSignature;
use std::collections::BTreeMap;

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
    pub types: BTreeMap<&'hir str, HirType<'hir>>,
    pub instances: Vec<HirInstance<'hir>>,
}

impl<'hir> HirModule<'hir> {
    pub fn new(signature: &'hir HirModuleSignature<'hir>, body: HirModuleBody<'hir>) -> Self {
        Self { signature, body }
    }
}
