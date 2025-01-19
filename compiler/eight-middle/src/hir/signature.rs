//! Public signatures for items belonging to a [`HirModule`].
//!
//! The types are spanned so that consumers of a module provide contextual information for
//! diagnostic handling or debugging purposes.

use crate::hir::ty::HirTy;
use eight_span::Span;
use std::collections::BTreeMap;

/// A signature representing the public surface of a module.
///
/// It should be noted that the module signature is actually not mutated after it has been derived
/// from the AST. This is because the signature acts as an API surface for the compiler. It is
/// intended to be query-only.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleSignature<'hir> {
    pub functions: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
    pub structs: BTreeMap<&'hir str, &'hir HirStructSignature<'hir>>,
    pub types: BTreeMap<&'hir str, &'hir HirTypeSignature<'hir>>,
    pub traits: BTreeMap<&'hir str, &'hir HirTraitSignature<'hir>>,
    /// Instances are stored in a flat list.
    ///
    /// Use the [`HirQueryDatabase`] to query instances by trait/types more efficiently.
    pub instances: Vec<&'hir HirInstanceSignature<'hir>>,
}

impl<'hir> HirModuleSignature<'hir> {
    pub fn add_function(&mut self, name: &'hir str, signature: &'hir HirFunctionSignature<'hir>) {
        self.functions.insert(name, signature);
    }

    pub fn add_struct(&mut self, name: &'hir str, signature: &'hir HirStructSignature<'hir>) {
        self.structs.insert(name, signature);
    }

    pub fn add_type(&mut self, name: &'hir str, signature: &'hir HirTypeSignature<'hir>) {
        self.types.insert(name, signature);
    }

    pub fn add_trait(&mut self, name: &'hir str, signature: &'hir HirTraitSignature<'hir>) {
        self.traits.insert(name, signature);
    }

    pub fn add_instance(&mut self, signature: &'hir HirInstanceSignature<'hir>) {
        self.instances.push(signature);
    }

    pub fn get_function(&self, name: &str) -> Option<&'hir HirFunctionSignature<'hir>> {
        self.functions.get(name).copied()
    }

    pub fn get_struct(&self, name: &str) -> Option<&'hir HirStructSignature<'hir>> {
        self.structs.get(name).copied()
    }

    pub fn get_type(&self, name: &str) -> Option<&'hir HirTypeSignature<'hir>> {
        self.types.get(name).copied()
    }

    pub fn get_trait(&self, name: &str) -> Option<&'hir HirTraitSignature<'hir>> {
        self.traits.get(name).copied()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirModuleItemSignature<'hir> {
    Function(&'hir HirFunctionSignature<'hir>),
    Struct(&'hir HirStructSignature<'hir>),
    Type(&'hir HirTypeSignature<'hir>),
    Trait(&'hir HirTraitSignature<'hir>),
    Instance(&'hir HirInstanceSignature<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub fields: BTreeMap<&'hir str, &'hir HirStructFieldSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructFieldSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
}

/// A signature for a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionSignature<'hir> {
    pub span: Span,
    pub parameters: Vec<&'hir HirFunctionParameterSignature<'hir>>,
    pub type_parameters: Vec<&'hir HirTypeParameterSignature<'hir>>,
    pub return_type: &'hir HirTy<'hir>,
    pub return_type_annotation: Option<Span>,
}

impl<'hir> HirFunctionSignature<'hir> {
    pub fn is_generic(&self) -> bool {
        !self.type_parameters.is_empty()
    }
}

/// A signature for a single parameter of a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameterSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

/// A signature for a type parameter of a trait or a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeParameterSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    /// The type-variable that this type parameter was assigned to.
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub type_parameters: Vec<&'hir HirTypeParameterSignature<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstanceSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub trait_name: &'hir str,
    pub trait_name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
}
