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
    functions: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
    records: BTreeMap<String, &'ta HirRecordApiSignature<'ta>>,
    scalars: BTreeMap<String, &'ta HirScalarApiSignature<'ta>>,
    traits: BTreeMap<String, &'ta HirTraitApiSignature<'ta>>,
    instances: BTreeMap<String, Vec<&'ta HirInstanceApiSignature<'ta>>>,
}

impl<'ta> HirModuleSignature<'ta> {
    /// Add the given function to the module signature.
    pub fn add_function(&mut self, name: &str, signature: &'ta HirFunctionApiSignature<'ta>) {
        self.functions.insert(name.to_owned(), signature);
    }

    /// Add the given record type to the module signature.
    pub fn add_record(&mut self, name: &str, signature: &'ta HirRecordApiSignature<'ta>) {
        self.records.insert(name.to_owned(), signature);
    }

    /// Add the given scalar type to the module signature.
    pub fn add_scalar(&mut self, name: &str, signature: &'ta HirScalarApiSignature<'ta>) {
        self.scalars.insert(name.to_owned(), signature);
    }

    /// Add the given trait to the
    pub fn add_trait(&mut self, name: &str, signature: &'ta HirTraitApiSignature<'ta>) {
        self.traits.insert(name.to_owned(), signature);
    }

    /// Add the given instance to the module signature.
    pub fn add_instance(&mut self, name: &str, signature: &'ta HirInstanceApiSignature<'ta>) {
        self.instances
            .entry(name.to_owned())
            .or_default()
            .push(signature);
    }

    /// Determine if a given type exists in the module signature.
    pub fn get_type_item(&self, name: &str) -> Option<HirModuleItemSignature<'ta>> {
        self.get_record(name)
            .map(HirModuleItemSignature::Record)
            .or_else(|| self.get_scalar(name).map(HirModuleItemSignature::Scalar))
    }

    /// Search for a function by name
    pub fn get_function(&self, name: &str) -> Option<&'ta HirFunctionApiSignature<'ta>> {
        self.functions.get(name).copied()
    }

    /// Search for a record type by name
    pub fn get_record(&self, name: &str) -> Option<&'ta HirRecordApiSignature<'ta>> {
        self.records.get(name).copied()
    }

    /// Search for a scalar type by name
    pub fn get_scalar(&self, name: &str) -> Option<&'ta HirScalarApiSignature<'ta>> {
        self.scalars.get(name).copied()
    }

    /// Iterate over all the functions in the module signature.
    pub fn functions(&self) -> impl Iterator<Item = (&String, &&'ta HirFunctionApiSignature<'ta>)> {
        self.functions.iter()
    }

    /// Iterate over all the records in the module signature.
    pub fn records(&self) -> impl Iterator<Item = (&String, &&'ta HirRecordApiSignature<'ta>)> {
        self.records.iter()
    }

    /// Iterate over all the scalars in the module signature.
    pub fn scalars(&self) -> impl Iterator<Item = (&String, &&'ta HirScalarApiSignature<'ta>)> {
        self.scalars.iter()
    }

    /// Iterate over all the traits in the module signature.
    pub fn traits(&self) -> impl Iterator<Item = (&String, &&'ta HirTraitApiSignature<'ta>)> {
        self.traits.iter()
    }

    /// Iterate over all the instances in the module signature.
    pub fn instances(
        &self,
    ) -> impl Iterator<Item = (&String, &Vec<&'ta HirInstanceApiSignature<'ta>>)> {
        self.instances.iter()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirModuleItemSignature<'ta> {
    Function(&'ta HirFunctionApiSignature<'ta>),
    Record(&'ta HirRecordApiSignature<'ta>),
    Scalar(&'ta HirScalarApiSignature<'ta>),
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
pub struct HirScalarApiSignature<'ta> {
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
    pub type_arguments: Vec<&'ta HirTy<'ta>>,
    pub methods: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
}
