use crate::HirName;
use eight_diagnostics::ice;
use std::fmt::{Debug, Display};
use std::hash::{DefaultHasher, Hash, Hasher};

/// An interned identifier for a type.
///
/// This is used to represent a HirTy in the [`HirArena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HirTyId(u64);

impl HirTyId {
    pub fn compute_integer32_ty_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x00.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_boolean_ty_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x01.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_unit_ty_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x02.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_variable_ty_id(var: usize) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x10, var).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_function_ty_id(return_type: &HirTyId, parameters: &[HirTyId]) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x20, return_type, parameters).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_pointer_ty_id(inner: &HirTyId) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x30, inner).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_nominal_ty_id(name: &str) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x40, name).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_uninitialized_ty_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x50.hash(&mut hasher);
        Self(hasher.finish())
    }
}

impl<'ta> From<&'ta HirTy<'ta>> for HirTyId {
    fn from(ty: &'ta HirTy<'ta>) -> Self {
        match ty {
            HirTy::Nominal(n) => HirTyId::compute_nominal_ty_id(n.name.name.as_str()),
            HirTy::Pointer(p) => HirTyId::compute_pointer_ty_id(&HirTyId::from(p.inner)),
            HirTy::Function(f) => {
                let parameters = f
                    .parameters
                    .iter()
                    .map(|p| HirTyId::from(*p))
                    .collect::<Vec<_>>();
                let return_type = HirTyId::from(f.return_type);
                HirTyId::compute_function_ty_id(&return_type, parameters.as_slice())
            }
            HirTy::Integer32(_) => HirTyId::compute_integer32_ty_id(),
            HirTy::Boolean(_) => HirTyId::compute_boolean_ty_id(),
            HirTy::Unit(_) => HirTyId::compute_unit_ty_id(),
            HirTy::Variable(v) => HirTyId::compute_variable_ty_id(v.var),
            HirTy::Uninitialized(_) => HirTyId::compute_uninitialized_ty_id(),
        }
    }
}

/// A single type in the HIR representation.
///
/// This is designed to be easily inferrable using a Hindley-Milner algorithm W implementation. We
/// extend the HM type system with a few additional features:
///
/// 1. Pointer and reference types, which effectively are Abs types.
/// 2. Record types, which are indexable abstract types.
#[must_use]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum HirTy<'ta> {
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
    Function(HirFunctionTy<'ta>),
    /// A pointer constructor type.
    ///
    /// The pointer has a single parameter type, which is the inner pointee type.
    Pointer(HirPointerTy<'ta>),
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
    Uninitialized(HirUninitializedTy),
}

impl<'ta> HirTy<'ta> {
    /// Determine if two types are trivially equal.
    ///
    /// Two types are trivially equal if they refer to the same type.
    pub fn is_trivially_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (HirTy::Boolean(_), HirTy::Boolean(_)) => true,
            (HirTy::Integer32(_), HirTy::Integer32(_)) => true,
            (HirTy::Unit(_), HirTy::Unit(_)) => true,
            (HirTy::Variable(v), HirTy::Variable(o)) => v.var == o.var,
            (HirTy::Pointer(v), HirTy::Pointer(o)) => v.inner.is_trivially_equal(o.inner),
            (HirTy::Function(v), HirTy::Function(o)) => {
                v.return_type.is_trivially_equal(o.return_type)
                    && v.parameters.len() == o.parameters.len()
                    && v.parameters
                        .iter()
                        .zip(o.parameters.iter())
                        .all(|(a, b)| a.is_trivially_equal(b))
            }
            (HirTy::Nominal(v), HirTy::Nominal(o)) => v.name.name == o.name.name,
            (HirTy::Uninitialized(_), HirTy::Uninitialized(_)) => {
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

impl Debug for HirTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Just use the Display implementation. We don't care enough for the spans here.
        write!(f, "{}", self)
    }
}

impl Display for HirTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirTy::Variable(t) => write!(f, "{}", t),
            HirTy::Function(t) => write!(f, "{}", t),
            HirTy::Integer32(t) => write!(f, "{}", t),
            HirTy::Boolean(t) => write!(f, "{}", t),
            HirTy::Unit(t) => write!(f, "{}", t),
            HirTy::Uninitialized(t) => write!(f, "{}", t),
            HirTy::Pointer(t) => write!(f, "{}", t),
            HirTy::Nominal(t) => write!(f, "{}", t),
        }
    }
}

impl HirTy<'_> {
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
        matches!(self, HirTy::Uninitialized(_))
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub struct HirInteger32Ty {}

impl Display for HirInteger32Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "i32")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub struct HirBooleanTy {}

impl Display for HirBooleanTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bool")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub struct HirUnitTy {}

impl Display for HirUnitTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unit")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirVariableTy {
    pub var: usize,
}

impl Display for HirVariableTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.var)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionTy<'ta> {
    pub return_type: &'ta HirTy<'ta>,
    pub parameters: Vec<&'ta HirTy<'ta>>,
}

impl Display for HirFunctionTy<'_> {
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
#[derive(Debug)]
pub struct HirPointerTy<'ta> {
    pub inner: &'ta HirTy<'ta>,
}

impl Display for HirPointerTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.inner)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirNominalTy {
    pub name: HirName,
}

impl Display for HirNominalTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.name)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirUninitializedTy {}

impl Display for HirUninitializedTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_")
    }
}
