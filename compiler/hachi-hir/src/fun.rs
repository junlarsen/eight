use crate::stmt::HirStmt;
use crate::ty::HirTy;
use crate::HirName;
use hachi_syntax::Span;

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
        matches!(self, HirFun::Function(HirFunction { type_parameters, .. }) if !type_parameters.is_empty())
    }

    pub fn type_parameters(&self) -> &Vec<Box<HirFunctionTypeParameter>> {
        match self {
            HirFun::Function(HirFunction {
                type_parameters, ..
            }) => type_parameters,
            HirFun::Intrinsic(HirIntrinsicFunction {
                type_parameters, ..
            }) => type_parameters,
        }
    }

    /// Get a reference to the function's parameters.
    pub fn parameters(&self) -> &Vec<Box<HirFunctionParameter>> {
        match self {
            HirFun::Function(HirFunction { parameters, .. }) => parameters,
            HirFun::Intrinsic(HirIntrinsicFunction { parameters, .. }) => parameters,
        }
    }

    /// Get a mutable reference to the function's parameters.
    pub fn parameters_mut(&mut self) -> &mut Vec<Box<HirFunctionParameter>> {
        match self {
            HirFun::Function(HirFunction { parameters, .. }) => parameters,
            HirFun::Intrinsic(HirIntrinsicFunction { parameters, .. }) => parameters,
        }
    }

    /// Get the function's return type.
    pub fn return_type(&self) -> &HirTy {
        match self {
            HirFun::Function(HirFunction { return_type, .. }) => return_type,
            HirFun::Intrinsic(HirIntrinsicFunction { return_type, .. }) => return_type,
        }
    }

    /// Get a mutable reference to the function's return type.
    pub fn return_type_mut(&mut self) -> &mut HirTy {
        match self {
            HirFun::Function(HirFunction { return_type, .. }) => return_type,
            HirFun::Intrinsic(HirIntrinsicFunction { return_type, .. }) => return_type,
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

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionTypeParameter {
    /// Span containing only the type parameter name.
    ///
    /// This is effectively the same as the span of the HirName, but in the future we may want to
    /// allow bounds or sub-typing on type parameters.
    pub span: Span,
    pub name: HirName,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameter {
    pub span: Span,
    pub name: HirName,
    pub ty: Box<HirTy>,
}
