use hachi_syntax::Span;
use std::collections::HashMap;
use std::fmt::Debug;

/// A single type in the HIR representation.
///
/// This is designed to be easily inferrable using a Hindley-Milner algorithm W implementation. We
/// extend the HM type system with a few additional features:
///
/// 1. Pointer and reference types, which effectively are Abs types.
/// 2. Record types, which are indexable abstract types.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirTy<'hir> {
    Var(TyVariable<'hir>),
    Fun(HirFunctionTy<'hir>),
    Const(HirConstantTy<'hir>),
    Ptr(HirPointerTy<'hir>),
    Ref(HirReferenceTy<'hir>),
    Record(HirRecordTy<'hir>),
    Uninitialized,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct TyVariable<'hir> {
    pub name: usize,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirFunctionTy<'hir> {
    pub return_type: &'hir HirTy<'hir>,
    pub parameters: Vec<&'hir HirTy<'hir>>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirConstantTy<'hir> {
    pub name: String,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirPointerTy<'hir> {
    pub inner: &'hir HirTy<'hir>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirReferenceTy<'hir> {
    pub inner: &'hir HirTy<'hir>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirRecordTy<'hir> {
    pub fields: HashMap<String, &'hir HirTy<'hir>>,
    pub span: Span,
}

impl<'hir> HirTy<'hir> {
    pub fn new_var(name: usize, span: Span) -> Self {
        Self::Var(TyVariable { name, span })
    }

    pub fn new_fun(
        return_type: &'hir HirTy<'hir>,
        parameters: Vec<&'hir HirTy<'hir>>,
        span: Span,
    ) -> Self {
        Self::Fun(HirFunctionTy {
            return_type,
            parameters,
            span,
        })
    }

    pub fn new_const(name: String, span: Span) -> Self {
        Self::Const(HirConstantTy { name, span })
    }

    pub fn new_ptr(inner: &'hir HirTy<'hir>, span: Span) -> Self {
        Self::Ptr(HirPointerTy { inner, span })
    }

    pub fn new_ref(inner: &'hir HirTy<'hir>, span: Span) -> Self {
        Self::Ref(HirReferenceTy { inner, span })
    }

    pub fn new_record(fields: HashMap<String, &'hir HirTy<'hir>>, span: Span) -> Self {
        Self::Record(HirRecordTy { fields, span })
    }
}

impl HirTy {
    pub fn is_intrinsic_i32(&self) -> bool {
        matches!(self, HirTy::Const(t) if t.name == "i32")
    }

    pub fn is_intrinsic_bool(&self) -> bool {
        matches!(self, HirTy::Const(t) if t.name == "bool")
    }

    pub fn is_intrinsic_void(&self) -> bool {
        matches!(self, HirTy::Const(t) if t.name == "void")
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self, HirTy::Ptr(_))
    }

    pub fn is_reference(&self) -> bool {
        matches!(self, HirTy::Ref(_))
    }

    pub fn is_record(&self) -> bool {
        matches!(self, HirTy::Record(_))
    }
}
