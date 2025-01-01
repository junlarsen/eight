use crate::{HirName, InternedTy};
use hachi_syntax::Span;

/// A function defined in a HIR module.
///
/// Functions are either user-defined with code, or forward-declared intrinsic functions. We do
/// currently not have any syntax to specify linkage types of intrinsic functions, so for now it's
/// safe to assume everything comes from if it's intrinsic.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirFun<'hir> {
    Function(HirFunction<'hir>),
    Intrinsic(HirIntrinsicFunction<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirFunction<'hir> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName<'hir>,
    pub type_parameters: Vec<HirTypeParameter<'hir>>,
    pub parameters: Vec<InternedTy<'hir>>,
    pub return_type: InternedTy<'hir>,
    pub body: Vec<InternedTy<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirIntrinsicFunction<'hir> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName<'hir>,
    pub type_parameters: Vec<HirTypeParameter<'hir>>,
    pub parameters: Vec<InternedTy<'hir>>,
    pub return_type: InternedTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirTypeParameter<'hir> {
    /// Span containing only the type parameter name.
    ///
    /// This is effectively the same as the span of the HirName, but in the future we may want to
    /// allow bounds or sub-typing on type parameters.
    pub span: Span,
    pub name: HirName<'hir>,
}
