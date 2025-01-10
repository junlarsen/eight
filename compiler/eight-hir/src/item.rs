use crate::signature::{
    HirFunctionApiSignature, HirInstanceApiSignature, HirRecordApiSignature, HirTraitApiSignature,
    HirTypeApiSignature,
};
use crate::stmt::HirStmt;
use crate::ty::HirTy;
use crate::{HirName, LinkageType};
use eight_span::Span;
use std::collections::BTreeMap;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntrinsicType<'ta> {
    pub span: Span,
    pub name: HirName,
    pub signature: &'ta HirTypeApiSignature<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirRecord<'ta> {
    /// Span encapsulating the entire record definition.
    pub span: Span,
    pub name: HirName,
    pub signature: &'ta HirRecordApiSignature<'ta>,
    pub instantiated_fields: BTreeMap<String, &'ta HirTy<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction<'ta> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub signature: &'ta HirFunctionApiSignature<'ta>,
    pub body: Vec<HirStmt<'ta>>,

    // TODO: Replace with OnceCell
    pub instantiated_return_type: Option<&'ta HirTy<'ta>>,
    pub instantiated_parameters: BTreeMap<String, &'ta HirTy<'ta>>,
    /// The type that was substituted in the current function.
    ///
    /// This is only for cosmetic purposes in the debug printing pass. This allows us to print the
    /// substituted variable for a function type parameter.
    ///
    /// ```text
    /// fn foo<T>(x: T) -> T {}
    ///
    /// // becomes
    /// fn foo<$0>(x: $0) -> $0 {}
    /// // or if the module is printed before type inference
    /// fn foo<T>(x: T) -> T {}
    /// ```
    pub type_parameter_substitutions: BTreeMap<String, &'ta HirTy<'ta>>,
    pub linkage_type: LinkageType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTrait<'ta> {
    pub span: Span,
    pub name: HirName,
    pub signature: &'ta HirTraitApiSignature<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitFunctionItem<'ta> {
    pub span: Span,
    pub name: HirName,
    pub signature: &'ta HirFunctionApiSignature<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstance<'ta> {
    pub span: Span,
    pub name: HirName,
    pub instantiation_type_parameters: Vec<&'ta HirTy<'ta>>,
    pub members: Vec<HirFunction<'ta>>,
    pub signature: &'ta HirInstanceApiSignature<'ta>,
}
