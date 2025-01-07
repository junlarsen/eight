use crate::stmt::HirStmt;
use crate::ty::HirTy;
use crate::HirName;
use hachi_span::Span;

/// A non-generalized function signature.
///
/// This type is used to represent functions in a Hir module, without having to copy over the entire
/// function body.
///
/// It also serves as a unified representation for both intrinsic and user-defined functions, as we
/// only store the types and parameters.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionSignature<'ta> {
    pub span: Span,
    pub type_parameters: Vec<HirFunctionTypeParameter>,
    pub parameters: Vec<HirFunctionParameter<'ta>>,
    pub return_type: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction<'ta> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub type_parameters: Vec<HirFunctionTypeParameter>,
    pub parameters: Vec<HirFunctionParameter<'ta>>,
    pub return_type: &'ta HirTy<'ta>,
    pub return_type_annotation: Option<Span>,
    pub body: Vec<HirStmt<'ta>>,
}

impl<'ta> HirFunction<'ta> {
    pub fn signature(&self) -> HirFunctionSignature<'ta> {
        let type_parameters = self.type_parameters.clone();
        let parameters = self.parameters.clone();
        let return_type = self.return_type;
        HirFunctionSignature {
            span: self.span,
            type_parameters,
            parameters,
            return_type,
        }
    }
}

impl<'ta> HirIntrinsicFunction<'ta> {
    pub fn signature(&self) -> HirFunctionSignature<'ta> {
        let type_parameters = self.type_parameters.clone();
        let parameters = self.parameters.clone();
        let return_type = self.return_type;
        HirFunctionSignature {
            span: self.span,
            type_parameters,
            parameters,
            return_type,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntrinsicFunction<'ta> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub type_parameters: Vec<HirFunctionTypeParameter>,
    pub parameters: Vec<HirFunctionParameter<'ta>>,
    pub return_type: &'ta HirTy<'ta>,
    pub return_type_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionTypeParameter {
    /// Span containing only the type parameter name.
    ///
    /// This is effectively the same as the span of the HirName, but in the future we may want to
    /// allow bounds or sub-typing on type parameters.
    pub span: Span,
    /// The name that was actually written by the programmer.
    pub syntax_name: HirName,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionParameter<'ta> {
    pub span: Span,
    pub name: HirName,
    pub r#type: &'ta HirTy<'ta>,
    pub type_annotation: Span,
}
