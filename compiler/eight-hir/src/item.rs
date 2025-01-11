use crate::signature::{
    HirFunctionApiSignature, HirInstanceApiSignature, HirStructApiSignature, HirTraitApiSignature,
    HirTypeApiSignature,
};
use crate::stmt::HirStmt;
use crate::ty::HirTy;
use crate::LinkageType;
use eight_span::Span;
use std::collections::BTreeMap;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntrinsicType<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirTypeApiSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStruct<'hir> {
    /// Span encapsulating the entire struct definition.
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirStructApiSignature<'hir>,
    pub instantiated_fields: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction<'hir> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirFunctionApiSignature<'hir>,
    pub body: Vec<HirStmt<'hir>>,

    // TODO: Replace with OnceCell
    pub instantiated_return_type: Option<&'hir HirTy<'hir>>,
    pub instantiated_parameters: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
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
    pub type_parameter_substitutions: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
    pub linkage_type: LinkageType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTrait<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirTraitApiSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitFunctionItem<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirFunctionApiSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstance<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub members: Vec<HirFunction<'hir>>,
    pub signature: &'hir HirInstanceApiSignature<'hir>,
}
