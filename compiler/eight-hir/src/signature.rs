//! Public API signatures for items belonging to a [`HirModule`].
//!
//! The types are spanned so that consumers of the API can provide contextual information for
//! diagnostic handling or debugging purposes.
//!
//! Note that this notion of API does not account for item visibility at the moment. This is because
//! there is no syntax for visibility in the language as of today.

use crate::ty::HirTy;
use crate::HirName;
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
    pub functions: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
    pub records: BTreeMap<String, &'ta HirRecordApiSignature<'ta>>,
    pub types: BTreeMap<String, &'ta HirTypeApiSignature<'ta>>,
    pub traits: BTreeMap<String, &'ta HirTraitApiSignature<'ta>>,
    /// Instances are stored in a flat list.
    ///
    /// Use the [`HirQueryDatabase`] to query instances by trait/types more efficiently.
    pub instances: Vec<&'ta HirInstanceApiSignature<'ta>>,
}

impl<'ta> HirModuleSignature<'ta> {
    pub fn add_function(&mut self, name: &str, signature: &'ta HirFunctionApiSignature<'ta>) {
        self.functions.insert(name.to_owned(), signature);
    }

    pub fn add_record(&mut self, name: &str, signature: &'ta HirRecordApiSignature<'ta>) {
        self.records.insert(name.to_owned(), signature);
    }

    pub fn add_type(&mut self, name: &str, signature: &'ta HirTypeApiSignature<'ta>) {
        self.types.insert(name.to_owned(), signature);
    }

    pub fn add_trait(&mut self, name: &str, signature: &'ta HirTraitApiSignature<'ta>) {
        self.traits.insert(name.to_owned(), signature);
    }

    pub fn add_instance(&mut self, signature: &'ta HirInstanceApiSignature<'ta>) {
        self.instances.push(signature);
    }

    pub fn get_function(&self, name: &str) -> Option<&'ta HirFunctionApiSignature<'ta>> {
        self.functions.get(name).copied()
    }

    pub fn get_record(&self, name: &str) -> Option<&'ta HirRecordApiSignature<'ta>> {
        self.records.get(name).copied()
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
    Record(&'ta HirRecordApiSignature<'ta>),
    Type(&'ta HirTypeApiSignature<'ta>),
    Trait(&'ta HirTraitApiSignature<'ta>),
    Instance(&'ta HirInstanceApiSignature<'ta>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirRecordApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub fields: BTreeMap<String, &'ta HirRecordFieldApiSignature<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirRecordFieldApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub ty: &'ta HirTy<'ta>,
    pub ty_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub ty: &'ta HirTy<'ta>,
}

/// A signature for a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionApiSignature<'ta> {
    pub span: Span,
    pub parameters: Vec<&'ta HirFunctionParameterApiSignature<'ta>>,
    pub type_parameters: Vec<&'ta HirTypeParameterApiSignature>,
    pub return_type: &'ta HirTy<'ta>,
    pub return_type_annotation: Option<Span>,
}

/// A signature for a single parameter of a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameterApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub ty: &'ta HirTy<'ta>,
    pub ty_annotation: Span,
}

/// A signature for a type parameter of a trait or a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeParameterApiSignature {
    pub span: Span,
    pub declaration_name: HirName,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub type_parameters: Vec<&'ta HirTypeParameterApiSignature>,
    pub methods: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstanceApiSignature<'ta> {
    pub span: Span,
    pub declaration_name: HirName,
    pub r#trait: HirName,
    pub type_arguments: Vec<&'ta HirTy<'ta>>,
    pub methods: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
}
