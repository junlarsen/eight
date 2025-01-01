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
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub enum HirTy {
    Variable(HirVariableTy),
    Function(HirFunctionTy),
    Constant(HirConstantTy),
    Pointer(HirPointerTy),
    Reference(HirReferenceTy),
    Record(HirRecordTy),
    Uninitialized,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirVariableTy {
    pub name: usize,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionTy {
    pub return_type: Box<HirTy>,
    pub parameters: Vec<Box<HirTy>>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirConstantTy {
    pub name: String,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirPointerTy {
    pub inner: Box<HirTy>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirReferenceTy {
    pub inner: Box<HirTy>,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirRecordTy {
    pub fields: HashMap<String, Box<HirTy>>,
    pub span: Span,
}

impl HirTy {
    pub fn new_var(name: usize, span: Span) -> Self {
        Self::Variable(HirVariableTy { name, span })
    }

    pub fn new_fun(return_type: Box<HirTy>, parameters: Vec<Box<HirTy>>, span: &Span) -> Self {
        Self::Function(HirFunctionTy {
            return_type,
            parameters,
            span: span.clone(),
        })
    }

    pub fn new_const<T: AsRef<str>>(name: T, span: &Span) -> Self {
        Self::Constant(HirConstantTy {
            name: name.as_ref().to_owned(),
            span: span.clone(),
        })
    }

    pub fn new_ptr(inner: Box<HirTy>, span: &Span) -> Self {
        Self::Pointer(HirPointerTy {
            inner,
            span: span.clone(),
        })
    }

    pub fn new_ref(inner: Box<HirTy>, span: &Span) -> Self {
        Self::Reference(HirReferenceTy {
            inner,
            span: span.clone(),
        })
    }

    pub fn new_record(fields: HashMap<String, Box<HirTy>>, span: &Span) -> Self {
        Self::Record(HirRecordTy {
            fields,
            span: span.clone(),
        })
    }
}

impl HirTy {
    pub fn is_intrinsic_i32(&self) -> bool {
        matches!(self, HirTy::Constant(t) if t.name == "i32")
    }

    pub fn is_intrinsic_bool(&self) -> bool {
        matches!(self, HirTy::Constant(t) if t.name == "bool")
    }

    pub fn is_intrinsic_void(&self) -> bool {
        matches!(self, HirTy::Constant(t) if t.name == "void")
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self, HirTy::Pointer(_))
    }

    pub fn is_reference(&self) -> bool {
        matches!(self, HirTy::Reference(_))
    }

    pub fn is_record(&self) -> bool {
        matches!(self, HirTy::Record(_))
    }
}
