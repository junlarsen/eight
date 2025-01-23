//! The High-level Intermediate Representation.

use crate::LinkageType;
use eight_diagnostics::ice;
use eight_span::Span;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display};
use std::hash::{DefaultHasher, Hash, Hasher};

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirExpr<'hir> {
    IntegerLiteral(HirIntegerLiteralExpr<'hir>),
    BooleanLiteral(HirBooleanLiteralExpr<'hir>),
    Assign(HirAssignExpr<'hir>),
    UnaryOp(HirUnaryOpExpr<'hir>),
    BinaryOp(HirBinaryOpExpr<'hir>),
    Reference(HirReferenceExpr<'hir>),
    CallableReference(HirCallableReferenceExpr<'hir>),
    ConstantIndex(HirConstantIndexExpr<'hir>),
    OffsetIndex(HirOffsetIndexExpr<'hir>),
    Call(HirCallExpr<'hir>),
    Construct(HirConstructExpr<'hir>),
    Group(HirGroupExpr<'hir>),
    AddressOf(HirAddressOfExpr<'hir>),
    Deref(HirDerefExpr<'hir>),
}

impl<'hir> HirExpr<'hir> {
    pub fn span(&self) -> Span {
        match self {
            HirExpr::IntegerLiteral(e) => e.span,
            HirExpr::BooleanLiteral(e) => e.span,
            HirExpr::Assign(e) => e.span,
            HirExpr::UnaryOp(e) => e.span,
            HirExpr::BinaryOp(e) => e.span,
            HirExpr::ConstantIndex(e) => e.span,
            HirExpr::OffsetIndex(e) => e.span,
            HirExpr::Call(e) => e.span,
            HirExpr::Construct(e) => e.span,
            HirExpr::Group(e) => e.span,
            HirExpr::Reference(e) => e.span,
            HirExpr::CallableReference(e) => e.span,
            HirExpr::AddressOf(e) => e.span,
            HirExpr::Deref(e) => e.span,
        }
    }

    pub fn ty(&self) -> &'hir HirTy<'hir> {
        match self {
            HirExpr::IntegerLiteral(e) => e.ty,
            HirExpr::BooleanLiteral(e) => e.ty,
            HirExpr::Assign(e) => e.ty,
            HirExpr::UnaryOp(e) => e.ty,
            HirExpr::BinaryOp(e) => e.ty,
            HirExpr::ConstantIndex(e) => e.ty,
            HirExpr::OffsetIndex(e) => e.ty,
            HirExpr::Call(e) => e.ty,
            HirExpr::Construct(e) => e.ty,
            HirExpr::Group(e) => e.ty,
            HirExpr::Reference(e) => e.ty,
            HirExpr::CallableReference(e) => e.ty,
            HirExpr::AddressOf(e) => e.ty,
            HirExpr::Deref(e) => e.ty,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntegerLiteralExpr<'hir> {
    pub span: Span,
    pub value: i32,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBooleanLiteralExpr<'hir> {
    pub span: Span,
    pub value: bool,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAssignExpr<'hir> {
    pub span: Span,
    pub lhs: Box<HirExpr<'hir>>,
    pub rhs: Box<HirExpr<'hir>>,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirUnaryOpExpr<'hir> {
    pub span: Span,
    pub operand: Box<HirExpr<'hir>>,
    pub op: HirUnaryOp,
    pub op_span: Span,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBinaryOpExpr<'hir> {
    pub span: Span,
    pub lhs: Box<HirExpr<'hir>>,
    pub rhs: Box<HirExpr<'hir>>,
    pub op: HirBinaryOp,
    pub op_span: Span,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAddressOfExpr<'hir> {
    pub span: Span,
    pub inner: Box<HirExpr<'hir>>,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirDerefExpr<'hir> {
    pub span: Span,
    pub inner: Box<HirExpr<'hir>>,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirReferenceExpr<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    /// The type of `name` in the current scope.
    pub ty: &'hir HirTy<'hir>,
    pub is_reference_to_function: bool,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirCallableReferenceExpr<'hir> {
    pub span: Span,
    pub symbol: HirCallableSymbol<'hir>,
    pub ty: &'hir HirTy<'hir>,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
}

/// A reference to a callable symbol.
///
/// A callable symbol is a function or a trait instance's implementation of a trait function. This
/// distinction from [`HirReferenceExpr`] is important because it allows us to distinguish between
/// values in scope and function, as well as making the distinction between trait functions and
/// regular functions.
///
/// TODO: Consider moving the enum variants into separate types.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirCallableSymbol<'hir> {
    /// A function defined in the current crate.
    ///
    /// Tuple of (name, name_span)
    Function(&'hir str, Span),
    /// A function defined in a specific trait instance
    ///
    /// Tuple of (trait_name, trait_arguments, name, name_span)
    TraitFunction(&'hir str, Vec<&'hir HirTy<'hir>>, &'hir str, Span),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirOffsetIndexExpr<'hir> {
    pub span: Span,
    pub origin: Box<HirExpr<'hir>>,
    pub index: Box<HirExpr<'hir>>,
    /// The type of the result of expression.
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstantIndexExpr<'hir> {
    pub span: Span,
    pub origin: Box<HirExpr<'hir>>,
    pub index: &'hir str,
    pub index_span: Span,
    /// The type of the result of expression.
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirCallExpr<'hir> {
    pub span: Span,
    pub callee: Box<HirExpr<'hir>>,
    pub arguments: Vec<HirExpr<'hir>>,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    /// The type of the result of the call expression.
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExpr<'hir> {
    pub span: Span,
    pub callee: &'hir HirTy<'hir>,
    pub arguments: Vec<HirConstructExprArgument<'hir>>,
    /// The returned type of the construct expression. (i.e., the type of the struct)
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExprArgument<'hir> {
    pub span: Span,
    pub field: &'hir str,
    pub field_span: Span,
    pub expr: Box<HirExpr<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirGroupExpr<'hir> {
    pub span: Span,
    pub inner: Box<HirExpr<'hir>>,
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirUnaryOp {
    Not,
    Neg,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
    And,
    Or,
}

/// A scalar type in the HIR.
///
/// Not to be confused with [`HirTy`], which is a type that can be used in HIR.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirType<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirTypeSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStruct<'hir> {
    /// Span encapsulating the entire struct definition.
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirStructSignature<'hir>,
    pub instantiated_fields: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunction<'hir> {
    /// Span encapsulating the entire function definition.
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirFunctionSignature<'hir>,
    pub body: Vec<HirStmt<'hir>>,

    /// The type that was substituted for the function return type.
    ///
    /// When a function is instantiated, if its type was a type parameter, we need to substitute it
    /// for a meta variable in the type checker.
    ///
    /// This field is never None after type checking.
    ///
    /// TODO: Replace with OnceCell
    pub instantiated_return_type: Option<&'hir HirTy<'hir>>,
    /// The same as `instantiated_return_type`, but for the function parameters.
    pub instantiated_parameters: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
    /// The type that was substituted in the current function.
    ///
    /// This is only for cosmetic purposes in the debug printing pass. This allows us to print the
    /// substituted variable for a function type parameter.
    ///
    /// ```text
    /// fn foo<T>(x: T) -> T {}
    ///
    /// // becomes
    /// fn foo<$0>(x: $0) -> $0 {}
    /// // or if the module is printed before type inference
    /// fn foo<T>(x: T) -> T {}
    /// ```
    pub type_parameter_substitutions: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
    pub linkage_type: LinkageType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTrait<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirTraitSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitFunctionItem<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub signature: &'hir HirFunctionSignature<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstance<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub members: Vec<HirFunction<'hir>>,
    pub signature: &'hir HirInstanceSignature<'hir>,
    /// See [`HirFunction::type_parameter_substitutions`] for explanation.
    ///
    /// These are instantiations from the trait itself. Separate ones will be created for each
    /// member.
    pub type_parameter_substitutions: BTreeMap<&'hir str, &'hir HirTy<'hir>>,
}

/// A module containing all the types and functions defined in a program.
///
/// We use a BTreeMap here instead of a HashMap to preserve the order of the types for when we're
/// emitting code.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirModule<'hir> {
    pub signature: &'hir HirModuleSignature<'hir>,
    pub body: HirModuleBody<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleBody<'hir> {
    pub functions: BTreeMap<&'hir str, HirFunction<'hir>>,
    pub structs: BTreeMap<&'hir str, HirStruct<'hir>>,
    pub traits: BTreeMap<&'hir str, HirTrait<'hir>>,
    pub types: BTreeMap<&'hir str, HirType<'hir>>,
    pub instances: Vec<HirInstance<'hir>>,
}

impl<'hir> HirModule<'hir> {
    pub fn new(signature: &'hir HirModuleSignature<'hir>, body: HirModuleBody<'hir>) -> Self {
        Self { signature, body }
    }
}

/// A signature representing the public surface of a module.
///
/// It should be noted that the module signature is actually not mutated after it has been derived
/// from the AST. This is because the signature acts as an API surface for the compiler. It is
/// intended to be query-only.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct HirModuleSignature<'hir> {
    pub functions: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
    pub structs: BTreeMap<&'hir str, &'hir HirStructSignature<'hir>>,
    pub types: BTreeMap<&'hir str, &'hir HirTypeSignature<'hir>>,
    pub traits: BTreeMap<&'hir str, &'hir HirTraitSignature<'hir>>,
    /// Instances are stored in a flat list.
    ///
    /// Use the [`HirQueryDatabase`] to query instances by trait/types more efficiently.
    pub instances: Vec<&'hir HirInstanceSignature<'hir>>,
}

impl<'hir> HirModuleSignature<'hir> {
    pub fn add_function(&mut self, name: &'hir str, signature: &'hir HirFunctionSignature<'hir>) {
        self.functions.insert(name, signature);
    }

    pub fn add_struct(&mut self, name: &'hir str, signature: &'hir HirStructSignature<'hir>) {
        self.structs.insert(name, signature);
    }

    pub fn add_type(&mut self, name: &'hir str, signature: &'hir HirTypeSignature<'hir>) {
        self.types.insert(name, signature);
    }

    pub fn add_trait(&mut self, name: &'hir str, signature: &'hir HirTraitSignature<'hir>) {
        self.traits.insert(name, signature);
    }

    pub fn add_instance(&mut self, signature: &'hir HirInstanceSignature<'hir>) {
        self.instances.push(signature);
    }

    pub fn get_function(&self, name: &str) -> Option<&'hir HirFunctionSignature<'hir>> {
        self.functions.get(name).copied()
    }

    pub fn get_struct(&self, name: &str) -> Option<&'hir HirStructSignature<'hir>> {
        self.structs.get(name).copied()
    }

    pub fn get_type(&self, name: &str) -> Option<&'hir HirTypeSignature<'hir>> {
        self.types.get(name).copied()
    }

    pub fn get_trait(&self, name: &str) -> Option<&'hir HirTraitSignature<'hir>> {
        self.traits.get(name).copied()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirModuleItemSignature<'hir> {
    Function(&'hir HirFunctionSignature<'hir>),
    Struct(&'hir HirStructSignature<'hir>),
    Type(&'hir HirTypeSignature<'hir>),
    Trait(&'hir HirTraitSignature<'hir>),
    Instance(&'hir HirInstanceSignature<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub fields: BTreeMap<&'hir str, &'hir HirStructFieldSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirStructFieldSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
}

/// A signature for a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionSignature<'hir> {
    pub span: Span,
    pub parameters: Vec<&'hir HirFunctionParameterSignature<'hir>>,
    pub type_parameters: Vec<&'hir HirTypeParameterSignature<'hir>>,
    pub return_type: &'hir HirTy<'hir>,
    pub return_type_annotation: Option<Span>,
}

impl<'hir> HirFunctionSignature<'hir> {
    pub fn is_generic(&self) -> bool {
        !self.type_parameters.is_empty()
    }
}

/// A signature for a single parameter of a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionParameterSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub ty_annotation: Span,
}

/// A signature for a type parameter of a trait or a function.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTypeParameterSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    /// The type-variable that this type parameter was assigned to.
    pub ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirTraitSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub type_parameters: Vec<&'hir HirTypeParameterSignature<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInstanceSignature<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub trait_name: &'hir str,
    pub trait_name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub methods: BTreeMap<&'hir str, &'hir HirFunctionSignature<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirStmt<'hir> {
    Let(HirLetStmt<'hir>),
    Loop(HirLoopStmt<'hir>),
    Expr(HirExprStmt<'hir>),
    Return(HirReturnStmt<'hir>),
    If(HirIfStmt<'hir>),
    Break(HirBreakStmt),
    Continue(HirContinueStmt),
    Block(HirBlockStmt<'hir>),
}

impl HirStmt<'_> {
    pub fn span(&self) -> Span {
        match self {
            HirStmt::Let(s) => s.span,
            HirStmt::Loop(s) => s.span,
            HirStmt::Expr(s) => s.span,
            HirStmt::Return(s) => s.span,
            HirStmt::If(s) => s.span,
            HirStmt::Break(s) => s.span,
            HirStmt::Continue(s) => s.span,
            HirStmt::Block(s) => s.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirLetStmt<'hir> {
    pub span: Span,
    pub name: &'hir str,
    pub name_span: Span,
    pub ty: &'hir HirTy<'hir>,
    pub type_annotation: Option<Span>,
    pub value: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIfStmt<'hir> {
    pub span: Span,
    pub condition: HirExpr<'hir>,
    pub happy_path: Vec<HirStmt<'hir>>,
    pub unhappy_path: Vec<HirStmt<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirExprStmt<'hir> {
    pub span: Span,
    pub expr: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirLoopStmt<'hir> {
    pub span: Span,
    /// The condition for the loop to continue.
    ///
    /// For infinite loops, this node should be a constant literal of boolean true.
    pub condition: HirExpr<'hir>,
    pub body: Vec<HirStmt<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBreakStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirContinueStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirReturnStmt<'hir> {
    pub span: Span,
    pub value: Option<HirExpr<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBlockStmt<'hir> {
    pub span: Span,
    pub body: Vec<HirStmt<'hir>>,
}

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

    pub fn compute_variable_ty_id(depth: u32, index: u32) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x10, depth, index).hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_meta_ty_id(index: u32) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x11, index).hash(&mut hasher);
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

impl<'hir> From<&'hir HirTy<'hir>> for HirTyId {
    fn from(ty: &'hir HirTy<'hir>) -> Self {
        match ty {
            HirTy::Nominal(n) => HirTyId::compute_nominal_ty_id(n.name),
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
            HirTy::Variable(v) => HirTyId::compute_variable_ty_id(v.depth, v.index),
            HirTy::Meta(v) => HirTyId::compute_meta_ty_id(v.index),
            HirTy::Uninitialized(_) => HirTyId::compute_uninitialized_ty_id(),
        }
    }
}

/// A single type in the HIR representation.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum HirTy<'hir> {
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
    /// $1@0, $2@4, etc.
    ///
    /// The first number represents the depth of the type variable, and the second number represents
    /// the index of the variable in the scope.
    Variable(HirVariableTy),
    /// A meta variable to be resolved during inference-time.
    Meta(HirMetaTy),
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
    Function(HirFunctionTy<'hir>),
    /// A pointer constructor type.
    ///
    /// The pointer has a single parameter type, which is the inner pointee type.
    Pointer(HirPointerTy<'hir>),
    /// A nominal type.
    ///
    /// This is used for structs at the moment, but could also be used for enums in the future.
    Nominal(HirNominalTy<'hir>),
    /// A type that has not yet been resolved.
    ///
    /// All uninitialized types are eliminated during type inference. This enum variant exists in
    /// order to allow the Hir to rewrite syntax, or add inferrable types to code that is not yet
    /// annotated.
    ///
    /// In the Hir textual_pass format, uninitialized types are represented as `_`. The following example
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

impl<'hir> HirTy<'hir> {
    /// Determine if two types are trivially equal.
    ///
    /// Two types are trivially equal if they refer to the same type.
    pub fn is_trivially_equal(&self, other: &Self) -> bool {
        match (self, other) {
            (HirTy::Boolean(_), HirTy::Boolean(_)) => true,
            (HirTy::Integer32(_), HirTy::Integer32(_)) => true,
            (HirTy::Unit(_), HirTy::Unit(_)) => true,
            (HirTy::Variable(v), HirTy::Variable(o)) => v.depth == o.depth && v.index == o.index,
            (HirTy::Pointer(v), HirTy::Pointer(o)) => v.inner.is_trivially_equal(o.inner),
            (HirTy::Function(v), HirTy::Function(o)) => {
                v.return_type.is_trivially_equal(o.return_type)
                    && v.parameters.len() == o.parameters.len()
                    && v.parameters
                        .iter()
                        .zip(o.parameters.iter())
                        .all(|(a, b)| a.is_trivially_equal(b))
            }
            (HirTy::Nominal(v), HirTy::Nominal(o)) => std::ptr::eq(v.name, o.name),
            (HirTy::Uninitialized(_), HirTy::Uninitialized(_)) => {
                ice!("attempted to compare uninitialized types")
            }
            _ => false,
        }
    }

    /// Is this type equal to a meta variable of the same index?
    pub fn is_equal_to_meta(&self, m: &HirMetaTy) -> bool {
        match self {
            HirTy::Meta(v) => std::ptr::eq(v, m),
            _ => false,
        }
    }

    /// Format a type that may contain substitution variables.
    ///
    /// This is used when a type is emitted in an error message at a point in time where all the
    /// types are not yet deducible. For example, in the following code snippet, the type `R` of
    /// `Add` is not yet deducible, because `R` is also used to infer the type of `k`.
    ///
    /// Because we're not interested in exposing De Bruijn indices to the user, we simply replace
    /// all to-be-deduced types with the placeholder type `_`.
    ///
    /// ```text
    /// trait Add<A, B, R> {
    ///   fn add(a: A, b: B) -> R;
    /// }
    ///
    /// instance Add<i32, i32, i32> {
    ///   fn add(a: i32, b: i32) -> i32 {
    ///     ...
    ///   }
    /// }
    ///
    /// fn test(a: i32, b: bool) {
    ///   let k = a + b;
    ///   // ^ produces an error for Add<i32, bool, $V> instance could not be found
    /// }
    /// ```
    pub fn format_substitutable_type(&self) -> String {
        match self {
            HirTy::Meta(_) => "_".to_owned(),
            HirTy::Function(f) => {
                let parameters = f
                    .parameters
                    .iter()
                    .map(|p| p.format_substitutable_type())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "fn({}) -> {}",
                    parameters,
                    f.return_type.format_substitutable_type()
                )
            }
            HirTy::Integer32(_) => "i32".to_owned(),
            HirTy::Boolean(_) => "bool".to_owned(),
            HirTy::Unit(_) => "unit".to_owned(),
            HirTy::Nominal(n) => n.name.to_owned(),
            HirTy::Pointer(p) => format!("*{}", p.inner.format_substitutable_type()),
            HirTy::Uninitialized(_) => ice!("attempted to format uninitialized type"),
            HirTy::Variable(_) => ice!("attempted to format variable type"),
        }
    }

    /// Format a list of type parameters with the semantics of `format_substitutable_type`.
    pub fn format_substitutable_type_parameter_list(parameters: &[&HirTy]) -> String {
        let arguments = parameters
            .iter()
            .map(|p| p.format_substitutable_type())
            .collect::<Vec<_>>()
            .join(", ");
        format!("<{}>", arguments)
    }

    /// Explicit shorthand for the `Display` implementation of `HirTy`.
    pub fn format(&self) -> String {
        self.to_string()
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
            HirTy::Meta(t) => write!(f, "{}", t),
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

    pub fn is_nominal(&self) -> bool {
        matches!(self, HirTy::Nominal(_))
    }

    pub fn is_uninitialized(&self) -> bool {
        matches!(self, HirTy::Uninitialized(_))
    }

    pub fn is_variable(&self) -> bool {
        matches!(self, HirTy::Variable(_))
    }

    pub fn is_meta(&self) -> bool {
        matches!(self, HirTy::Meta(_))
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirInteger32Ty {}

impl Display for HirInteger32Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "i32")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBooleanTy {}

impl Display for HirBooleanTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bool")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirUnitTy {}

impl Display for HirUnitTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unit")
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirVariableTy {
    pub depth: u32,
    pub index: u32,
}

impl Display for HirVariableTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}'{}", self.depth, self.index)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirFunctionTy<'hir> {
    pub return_type: &'hir HirTy<'hir>,
    pub parameters: Vec<&'hir HirTy<'hir>>,
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
pub struct HirPointerTy<'hir> {
    pub inner: &'hir HirTy<'hir>,
}

impl Display for HirPointerTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.inner)
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirNominalTy<'hir> {
    pub name: &'hir str,
    pub name_span: Span,
}

impl<'hir> Display for HirNominalTy<'hir> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
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

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirMetaTy {
    pub index: u32,
}

impl Display for HirMetaTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.index)
    }
}
