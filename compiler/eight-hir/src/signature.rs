//! Public API signatures for items belonging to a [`HirModule`].
//!
//! The types are spanned so that consumers of the API can provide contextual information for
//! diagnostic handling or debugging purposes.
//!
//! Note that this notion of API does not account for item visibility at the moment. This is because
//! there is no syntax for visibility in the language as of today.

use crate::ty::HirTy;
use eight_span::Span;
use std::collections::BTreeMap;

/// A signature representing the public API of a module.
///
/// It should be noted that the module signature is actually not mutated after it has been derived
/// from the AST. This is because the signature acts as an API surface for the compiler. It is
/// intended to be query-only.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleSignature<'hir> {
    pub functions: BTreeMap<&'hir str, &'hir HirFunctionApiSignature<'hir>>,
    pub structs: BTreeMap<&'hir str, &'hir HirStructApiSignature<'hir>>,
    pub types: BTreeMap<&'hir str, &'hir HirTypeApiSignature<'hir>>,
    pub traits: BTreeMap<&'hir str, &'hir HirTraitApiSignature<'hir>>,
    /// Instances are stored in a flat list.
    ///
    /// Use the [`HirQueryDatabase`] to query instances by trait/types more efficiently.
    pub instances: Vec<&'hir HirInstanceApiSignature<'hir>>,
}

impl<'hir> HirModuleSignature<'hir> {
    pub fn add_function(
        &mut self,
        name: &'hir str,
        signature: &'hir HirFunctionApiSignature<'hir>,
    ) {
        self.functions.insert(name, signature);
    }

    pub fn add_struct(&mut self, name: &'hir str, signature: &'hir HirStructApiSignature<'hir>) {
        self.structs.insert(name, signature);
    }

    pub fn add_type(&mut self, name: &'hir str, signature: &'hir HirTypeApiSignature<'hir>) {
        self.types.insert(name, signature);
    }

    pub fn add_trait(&mut self, name: &'hir str, signature: &'hir HirTraitApiSignature<'hir>) {
        self.traits.insert(name, signature);
    }

    pub fn add_instance(&mut self, signature: &'hir HirInstanceApiSignature<'hir>) {
        self.instances.push(signature);
    }

    pub fn get_function(&self, name: &str) -> Option<&'hir HirFunctionApiSignature<'hir>> {
        self.functions.get(name).copied()
    }

    pub fn get_struct(&self, name: &str) -> Option<&'hir HirStructApiSignature<'hir>> {
        self.structs.get(name).copied()
    }

    pub fn get_type(&self, name: &str) -> Option<&'hir HirTypeApiSignature<'hir>> {
        self.types.get(name).copied()
    }

    pub fn get_trait(&self, name: &str) -> Option<&'hir HirTraitApiSignature<'hir>> {
        self.traits.get(name).copied()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirModuleItemSignature<'hir> {
    Function(&'hir HirFunctionApiSignature<'hir>),
    Struct(&'hir HirStructApiSignature<'hir>),
    Type(&'hir HirTypeApiSignature<'hir>),
    Trait(&'hir HirTraitApiSignature<'hir>),
    Instance(&'hir HirInstanceApiSignature<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub fields: BTreeMap<&'hir str, &'hir HirStructFieldApiSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructFieldApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
}

/// A signature for a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionApiSignature<'hir> {
    pub span: Span,
    pub parameters: Vec<&'hir HirFunctionParameterApiSignature<'hir>>,
    pub type_parameters: Vec<&'hir HirTypeParameterApiSignature<'hir>>,
    pub return_type: &'hir HirTy<'hir>,
    pub return_type_annotation: Option<Span>,
}

/// A signature for a single parameter of a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameterApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

/// A signature for a type parameter of a trait or a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeParameterApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub type_parameters: Vec<&'hir HirTypeParameterApiSignature<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionApiSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstanceApiSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub trait_name: &'hir str,
    pub trait_name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionApiSignature<'hir>>,
}
