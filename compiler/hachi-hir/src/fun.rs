use crate::stmt::HirStmt;
use crate::ty::{HirFunctionTy, HirTy};
use crate::HirName;
use hachi_span::Span;

/// A function defined in a HIR module.
///
/// Functions are either user-defined with code, or forward-declared intrinsic functions. We do
/// currently not have any syntax to specify linkage types of intrinsic functions, so for now it's
/// safe to assume everything comes from if it's intrinsic.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirFun {
    Function(HirFunction),
    Intrinsic(HirIntrinsicFunction),
}

impl HirFun {
    pub fn is_intrinsic(&self) -> bool {
        matches!(self, HirFun::Intrinsic(_))
    }

    /// Determine if the function has type parameters.
    pub fn has_type_parameters(&self) -> bool {
        match self {
            HirFun::Function(f) => !f.type_parameters.is_empty(),
            HirFun::Intrinsic(f) => !f.type_parameters.is_empty(),
        }
    }

    pub fn name(&self) -> &HirName {
        match self {
            HirFun::Function(f) => &f.name,
            HirFun::Intrinsic(f) => &f.name,
        }
    }

    /// Derive a function type matching the function's signature.
    pub fn get_type(&self) -> HirFunctionTy {
        match self {
            HirFun::Function(f) => f.get_type(),
            HirFun::Intrinsic(f) => f.get_type(),
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub type_parameters: Vec<Box<HirFunctionTypeParameter>>,
    pub parameters: Vec<Box<HirFunctionParameter>>,
    pub return_type: Box<HirTy>,
    pub body: Vec<Box<HirStmt>>,
}

impl HirFunction {
    pub fn get_type(&self) -> HirFunctionTy {
        HirFunctionTy {
            return_type: self.return_type.clone(),
            parameters: self.parameters.iter().map(|p| p.ty.clone()).collect(),
            span: self.span.clone(),
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntrinsicFunction {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub type_parameters: Vec<Box<HirFunctionTypeParameter>>,
    pub parameters: Vec<Box<HirFunctionParameter>>,
    pub return_type: Box<HirTy>,
}

impl HirIntrinsicFunction {
    pub fn get_type(&self) -> HirFunctionTy {
        HirFunctionTy {
            return_type: self.return_type.clone(),
            parameters: self.parameters.iter().map(|p| p.ty.clone()).collect(),
            span: self.span.clone(),
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionTypeParameter {
    /// Span containing only the type parameter name.
    ///
    /// This is effectively the same as the span of the HirName, but in the future we may want to
    /// allow bounds or sub-typing on type parameters.
    pub span: Span,
    /// The type variable index in the type environment.
    pub name: usize,
    /// The name that was actually written by the programmer.
    pub syntax_name: HirName,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionParameter {
    pub span: Span,
    pub name: HirName,
    pub ty: Box<HirTy>,
}
