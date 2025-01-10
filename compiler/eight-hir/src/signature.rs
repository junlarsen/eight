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
pub struct HirModuleSignature<'ta> {
    pub functions: BTreeMap<&'ta str, &'ta HirFunctionApiSignature<'ta>>,
    pub structs: BTreeMap<&'ta str, &'ta HirStructApiSignature<'ta>>,
    pub types: BTreeMap<&'ta str, &'ta HirTypeApiSignature<'ta>>,
    pub traits: BTreeMap<&'ta str, &'ta HirTraitApiSignature<'ta>>,
    /// Instances are stored in a flat list.
    ///
    /// Use the [`HirQueryDatabase`] to query instances by trait/types more efficiently.
    pub instances: Vec<&'ta HirInstanceApiSignature<'ta>>,
}

impl<'ta> HirModuleSignature<'ta> {
    pub fn add_function(&mut self, name: &'ta str, signature: &'ta HirFunctionApiSignature<'ta>) {
        self.functions.insert(name, signature);
    }

    pub fn add_struct(&mut self, name: &'ta str, signature: &'ta HirStructApiSignature<'ta>) {
        self.structs.insert(name, signature);
    }

    pub fn add_type(&mut self, name: &'ta str, signature: &'ta HirTypeApiSignature<'ta>) {
        self.types.insert(name, signature);
    }

    pub fn add_trait(&mut self, name: &'ta str, signature: &'ta HirTraitApiSignature<'ta>) {
        self.traits.insert(name, signature);
    }

    pub fn add_instance(&mut self, signature: &'ta HirInstanceApiSignature<'ta>) {
        self.instances.push(signature);
    }

    pub fn get_function(&self, name: &str) -> Option<&'ta HirFunctionApiSignature<'ta>> {
        self.functions.get(name).copied()
    }

    pub fn get_struct(&self, name: &str) -> Option<&'ta HirStructApiSignature<'ta>> {
        self.structs.get(name).copied()
    }

    pub fn get_type(&self, name: &str) -> Option<&'ta HirTypeApiSignature<'ta>> {
        self.types.get(name).copied()
    }

    pub fn get_trait(&self, name: &str) -> Option<&'ta HirTraitApiSignature<'ta>> {
        self.traits.get(name).copied()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirModuleItemSignature<'ta> {
    Function(&'ta HirFunctionApiSignature<'ta>),
    Struct(&'ta HirStructApiSignature<'ta>),
    Type(&'ta HirTypeApiSignature<'ta>),
    Trait(&'ta HirTraitApiSignature<'ta>),
    Instance(&'ta HirInstanceApiSignature<'ta>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub fields: BTreeMap<&'ta str, &'ta HirStructFieldApiSignature<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructFieldApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub ty: &'ta HirTy<'ta>,
    pub ty_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub ty: &'ta HirTy<'ta>,
}

/// A signature for a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionApiSignature<'ta> {
    pub span: Span,
    pub parameters: Vec<&'ta HirFunctionParameterApiSignature<'ta>>,
    pub type_parameters: Vec<&'ta HirTypeParameterApiSignature<'ta>>,
    pub return_type: &'ta HirTy<'ta>,
    pub return_type_annotation: Option<Span>,
}

/// A signature for a single parameter of a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameterApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub ty: &'ta HirTy<'ta>,
    pub ty_annotation: Span,
}

/// A signature for a type parameter of a trait or a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeParameterApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub type_parameters: Vec<&'ta HirTypeParameterApiSignature<'ta>>,
    pub methods: BTreeMap<&'ta str, &'ta HirFunctionApiSignature<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstanceApiSignature<'ta> {
    pub span: Span,
    pub name: &'ta str,
    pub name_span: Span,
    pub trait_name: &'ta str,
    pub trait_name_span: Span,
    pub type_arguments: Vec<&'ta HirTy<'ta>>,
    pub methods: BTreeMap<&'ta str, &'ta HirFunctionApiSignature<'ta>>,
}
