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
///
/// TODO: Intern these types in the HirArena
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleSignature<'ta> {
    pub functions: BTreeMap<String, &'ta HirFunctionApiSignature<'ta>>,
    pub records: BTreeMap<String, &'ta HirRecordApiSignature<'ta>>,
    pub scalars: BTreeMap<String, &'ta HirScalarApiSignature<'ta>>,
    pub traits: BTreeMap<String, &'ta HirTraitApiSignature<'ta>>,
    pub instances: BTreeMap<String, Vec<&'ta HirInstanceApiSignature<'ta>>>,
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
