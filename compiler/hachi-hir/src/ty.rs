use crate::HirName;
use hachi_diagnostics::ice;
use std::fmt::{Debug, Display};

/// A single type in the HIR representation.
///
/// This is designed to be easily inferrable using a Hindley-Milner algorithm W implementation. We
/// extend the HM type system with a few additional features:
///
/// 1. Pointer and reference types, which effectively are Abs types.
/// 2. Record types, which are indexable abstract types.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Clone)]
pub enum HirTy {
    /// The builtin type `i32`.
    Integer32(HirInteger32Ty),
    /// The builtin type `bool`.
    Boolean(HirBooleanTy),
    /// The builtin type `unit`.
    ///
    /// Signifies that a function does not return a value.
    Unit(HirUnitTy),
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
    /// A pointer constructor type.
    ///
    /// The pointer has a single parameter type, which is the inner pointee type.
    Pointer(HirPointerTy),
    /// A nominal type.
    ///
    /// This is used for structs at the moment, but could also be used for enums in the future.
    Nominal(HirNominalTy),
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
            (HirTy::Boolean(_), HirTy::Boolean(_)) => true,
            (HirTy::Integer32(_), HirTy::Integer32(_)) => true,
            (HirTy::Unit(_), HirTy::Unit(_)) => true,
            (HirTy::Variable(v), HirTy::Variable(o)) => v.var == o.var,
            (HirTy::Pointer(v), HirTy::Pointer(o)) => v.inner.is_trivially_equal(&o.inner),
            (HirTy::Function(v), HirTy::Function(o)) => {
                v.return_type.is_trivially_equal(&o.return_type)
                    && v.parameters.len() == o.parameters.len()
                    && v.parameters
                        .iter()
                        .zip(o.parameters.iter())
                        .all(|(a, b)| a.is_trivially_equal(b))
            }
            (HirTy::Nominal(v), HirTy::Nominal(o)) => v.name.name == o.name.name,
            (HirTy::Uninitialized, HirTy::Uninitialized) => {
                ice!("attempted to compare uninitialized types")
            }
            _ => false,
        }
    }

    pub fn is_equal_to_variable(&self, var: usize) -> bool {
        match self {
            HirTy::Variable(v) => v.var == var,
            _ => false,
        }
    }
}

impl HirTy {
    /// Create a new variable type.
    pub fn new_var(var: usize) -> Self {
        Self::Variable(HirVariableTy { var })
    }

    /// Create a new function type.
    pub fn new_fun(return_type: Box<HirTy>, parameters: Vec<Box<HirTy>>) -> Self {
        Self::Function(HirFunctionTy {
            return_type,
            parameters,
        })
    }

    /// Create a new pointer type.
    pub fn new_ptr(inner: Box<HirTy>) -> Self {
        Self::Pointer(HirPointerTy { inner })
    }

    /// Create a new nominal type.
    pub fn new_nominal(name: HirName) -> Self {
        Self::Nominal(HirNominalTy { name })
    }

    pub fn new_i32() -> Self {
        Self::Integer32(HirInteger32Ty {})
    }

    pub fn new_bool() -> Self {
        Self::Boolean(HirBooleanTy {})
    }

    pub fn new_unit() -> Self {
        Self::Unit(HirUnitTy {})
    }
}

impl Debug for HirTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Just use the Display implementation. We don't care enough for the spans here.
        write!(f, "{}", self)
    }
}

impl Display for HirTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirTy::Variable(t) => write!(f, "{}", t),
            HirTy::Function(t) => write!(f, "{}", t),
            HirTy::Integer32(t) => write!(f, "{}", t),
            HirTy::Boolean(t) => write!(f, "{}", t),
            HirTy::Unit(t) => write!(f, "{}", t),
            HirTy::Uninitialized => write!(f, "_"),
            HirTy::Pointer(t) => write!(f, "{}", t),
            HirTy::Nominal(t) => write!(f, "{}", t),
        }
    }
}

impl HirTy {
    pub fn is_intrinsic_i32(&self) -> bool {
        matches!(self, HirTy::Integer32(_))
    }

    pub fn is_intrinsic_bool(&self) -> bool {
        matches!(self, HirTy::Boolean(_))
    }

    pub fn is_intrinsic_unit(&self) -> bool {
        matches!(self, HirTy::Unit(_))
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self, HirTy::Pointer(_))
    }

    pub fn is_record(&self) -> bool {
        matches!(self, HirTy::Nominal(_))
    }

    pub fn is_uninitialized(&self) -> bool {
        matches!(self, HirTy::Uninitialized)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirInteger32Ty {}

impl Display for HirInteger32Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "i32")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirBooleanTy {}

impl Display for HirBooleanTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bool")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirUnitTy {}

impl Display for HirUnitTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unit")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirVariableTy {
    pub var: usize,
}

impl Display for HirVariableTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.var)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirFunctionTy {
    pub return_type: Box<HirTy>,
    pub parameters: Vec<Box<HirTy>>,
}

impl Display for HirFunctionTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self
            .parameters
            .iter()
            .map(|p| format!("{}", p))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "fn({}) -> {:?}", params, self.return_type)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirPointerTy {
    pub inner: Box<HirTy>,
}

impl Display for HirPointerTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.inner)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Clone)]
pub struct HirNominalTy {
    pub name: HirName,
}

impl Display for HirNominalTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.name)
    }
}
