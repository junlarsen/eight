use crate::stmt::HirStmt;
use crate::ty::{HirFunctionTy, HirTy};
use crate::HirName;
use hachi_span::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: HirName,
    pub type_parameters: Vec<Box<HirFunctionTypeParameter>>,
    pub parameters: Vec<Box<HirFunctionParameter>>,
    pub return_type: Box<HirTy>,
    pub return_type_annotation: Option<Span>,
    pub body: Vec<Box<HirStmt>>,
}

impl HirFunction {
    pub fn get_type(&self) -> HirFunctionTy {
        HirFunctionTy {
            return_type: self.return_type.clone(),
            parameters: self.parameters.iter().map(|p| p.r#type.clone()).collect(),
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
    pub return_type_annotation: Span,
}

impl HirIntrinsicFunction {
    pub fn get_type(&self) -> HirFunctionTy {
        HirFunctionTy {
            return_type: self.return_type.clone(),
            parameters: self.parameters.iter().map(|p| p.r#type.clone()).collect(),
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
    /// The name that was actually written by the programmer.
    pub syntax_name: HirName,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionParameter {
    pub span: Span,
    pub name: HirName,
    pub r#type: Box<HirTy>,
    pub type_annotation: Span,
}
