use hachi_syntax::Span;
use std::collections::BTreeMap;
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
    /// A type variable that is not yet resolved.
    ///
    /// These types are used for unification during type inference, and in the module IR look like
    /// $1, $2, etc.
    Variable(HirVariableTy),
    /// A function constructor type.
    ///
    /// This represents a function type with zero or more parameters and a return type. We do not
    /// need to encode the type parameters that the function respond to. The signature instead holds
    /// [`HirVariableTy`] types for types that represent generic type parameters.
    ///
    /// This makes the inference algorithm consistent, and we don't need to worry about tracking
    /// type parameter names in the type checker.
    ///
    /// Effectively, this means that HirFunctionTy is a rewrite of the following:
    ///
    /// ```text
    /// fn<T, U>(a: T, b: T, c: U) -> U
    ///
    /// HirFunctionTy {
    ///   return_type: $1,
    ///   parameters: [$1, $1, $2],
    /// }
    /// ```
    ///
    /// This type is also capable of representing partially parameterized functions, such as:
    ///
    /// ```text
    /// fn<T>(a: i32) -> T
    ///
    /// HirFunctionTy {
    ///   return_type: $1,
    ///   parameters: [HirConstantTy("i32")],
    /// }
    /// ```
    Function(HirFunctionTy),
    /// A constant constructor type.
    ///
    /// This represents a type that doesn't have any parameters. This container is used for scalar
    /// types such as i32, bool, and the special type void.
    Constant(HirConstantTy),
    /// A pointer constructor type.
    ///
    /// The pointer has a single parameter type, which is the inner pointee type.
    Pointer(HirPointerTy),
    /// A reference constructor type.
    ///
    /// The reference has a single parameter type, which is the referent type.
    Reference(HirReferenceTy),
    /// A record constructor type.
    ///
    /// We do not currently support parameterized records, so this type is effectively a quantified
    /// version of the HirConstantTy type.
    ///
    /// A HirRecordTy represents a packed type, and it can be indexed by any of its members to
    /// reveal the type of the field.
    Record(HirRecordTy),
    /// A type that has not yet been resolved.
    ///
    /// All uninitialized types are eliminated during type inference. This enum variant exists in
    /// order to allow the Hir to rewrite syntax, or add inferrable types to code that is not yet
    /// annotated.
    ///
    /// In the Hir textual format, uninitialized types are represented as `_`. The following example
    /// informs the type checker that the type of `x` was not provided by the programmer, and that
    /// it should be inferred to be `i32`.
    ///
    /// ```text
    /// let x: _ = 1;
    /// ```
    ///
    /// All expressions are also initially typed as uninitialized types.
    Uninitialized,
}

impl HirTy {
    /// Determine if two types are trivially equal.
    ///
    /// Two types are trivially equal if they refer to the same type.
    pub fn is_trivially_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (HirTy::Variable(v), HirTy::Variable(o)) => v.name == o.name,
            (HirTy::Pointer(v), HirTy::Pointer(o)) => v.inner.is_trivially_equal(&o.inner),
            (HirTy::Reference(v), HirTy::Reference(o)) => v.inner.is_trivially_equal(&o.inner),
            (HirTy::Constant(v), HirTy::Constant(o)) => v.name == o.name,
            (HirTy::Function(v), HirTy::Function(o)) => {
                v.return_type.is_trivially_equal(&o.return_type)
                    && v.parameters.len() == o.parameters.len()
                    && v.parameters
                        .iter()
                        .zip(o.parameters.iter())
                        .all(|(a, b)| a.is_trivially_equal(b))
            }
            (HirTy::Record(v), HirTy::Record(o)) => v
                .fields
                .iter()
                .all(|(k, v)| matches!(o.fields.get(k), Some(f) if f.is_trivially_equal(v))),
            (HirTy::Uninitialized, HirTy::Uninitialized) => {
                panic!("should not be comparing uninitialized types")
            }
            _ => false,
        }
    }
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

    pub fn new_record(fields: BTreeMap<String, Box<HirTy>>, span: &Span) -> Self {
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

    pub fn is_uninitialized(&self) -> bool {
        matches!(self, HirTy::Uninitialized)
    }

    pub fn is_exact_constant<T: AsRef<str>>(&self, m: T) -> bool {
        matches!(self, HirTy::Constant(HirConstantTy { name, .. }) if name == m.as_ref())
    }

    pub fn span(&self) -> &Span {
        match self {
            HirTy::Variable(v) => &v.span,
            HirTy::Function(f) => &f.span,
            HirTy::Constant(c) => &c.span,
            HirTy::Pointer(p) => &p.span,
            HirTy::Reference(r) => &r.span,
            HirTy::Record(r) => &r.span,
            HirTy::Uninitialized => todo!(),
        }
    }
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

impl HirReferenceTy {
    pub fn get_inner(&self) -> &HirTy {
        &self.inner
    }

    pub fn get_deep_inner(&self) -> &HirTy {
        match self.inner.as_ref() {
            HirTy::Reference(t) => t.get_deep_inner(),
            t => t,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirRecordTy {
    pub fields: BTreeMap<String, Box<HirTy>>,
    pub span: Span,
}
