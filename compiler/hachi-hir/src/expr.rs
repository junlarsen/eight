use crate::ty::HirTy;
use crate::HirName;
use hachi_span::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirExpr<'ta> {
    IntegerLiteral(HirIntegerLiteralExpr<'ta>),
    BooleanLiteral(HirBooleanLiteralExpr<'ta>),
    Assign(HirAssignExpr<'ta>),
    UnaryOp(HirUnaryOpExpr<'ta>),
    BinaryOp(HirBinaryOpExpr<'ta>),
    Reference(HirReferenceExpr<'ta>),
    ConstantIndex(HirConstantIndexExpr<'ta>),
    OffsetIndex(HirOffsetIndexExpr<'ta>),
    Call(HirCallExpr<'ta>),
    Construct(HirConstructExpr<'ta>),
    Group(HirGroupExpr<'ta>),
    AddressOf(HirAddressOfExpr<'ta>),
    Deref(HirDerefExpr<'ta>),
}

impl<'ta> HirExpr<'ta> {
    pub fn span(&self) -> &Span {
        match self {
            HirExpr::IntegerLiteral(e) => &e.span,
            HirExpr::BooleanLiteral(e) => &e.span,
            HirExpr::Assign(e) => &e.span,
            HirExpr::UnaryOp(e) => &e.span,
            HirExpr::BinaryOp(e) => &e.span,
            HirExpr::ConstantIndex(e) => &e.span,
            HirExpr::OffsetIndex(e) => &e.span,
            HirExpr::Call(e) => &e.span,
            HirExpr::Construct(e) => &e.span,
            HirExpr::Group(e) => &e.span,
            HirExpr::Reference(e) => &e.span,
            HirExpr::AddressOf(e) => &e.span,
            HirExpr::Deref(e) => &e.span,
        }
    }

    pub fn ty(&self) -> &'ta HirTy<'ta> {
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
            HirExpr::AddressOf(e) => e.ty,
            HirExpr::Deref(e) => e.ty,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntegerLiteralExpr<'ta> {
    pub span: Span,
    pub value: i32,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBooleanLiteralExpr<'ta> {
    pub span: Span,
    pub value: bool,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAssignExpr<'ta> {
    pub span: Span,
    pub lhs: Box<HirExpr<'ta>>,
    pub rhs: Box<HirExpr<'ta>>,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirUnaryOpExpr<'ta> {
    pub span: Span,
    pub operand: Box<HirExpr<'ta>>,
    pub op: HirUnaryOp,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBinaryOpExpr<'ta> {
    pub span: Span,
    pub lhs: Box<HirExpr<'ta>>,
    pub rhs: Box<HirExpr<'ta>>,
    pub op: HirBinaryOp,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAddressOfExpr<'ta> {
    pub span: Span,
    pub inner: Box<HirExpr<'ta>>,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirDerefExpr<'ta> {
    pub span: Span,
    pub inner: Box<HirExpr<'ta>>,
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirReferenceExpr<'ta> {
    pub span: Span,
    pub name: HirName,
    /// The type of `name` in the current scope.
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirOffsetIndexExpr<'ta> {
    pub span: Span,
    pub origin: Box<HirExpr<'ta>>,
    pub index: Box<HirExpr<'ta>>,
    /// The type of the result of expression.
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstantIndexExpr<'ta> {
    pub span: Span,
    pub origin: Box<HirExpr<'ta>>,
    pub index: HirName,
    /// The type of the result of expression.
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirCallExpr<'ta> {
    pub span: Span,
    pub callee: Box<HirExpr<'ta>>,
    pub arguments: Vec<Box<HirExpr<'ta>>>,
    pub type_arguments: Vec<&'ta HirTy<'ta>>,
    /// The type of the result of the call expression.
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExpr<'ta> {
    pub span: Span,
    pub callee: &'ta HirTy<'ta>,
    pub arguments: Vec<HirConstructExprArgument<'ta>>,
    /// The returned type of the construct expression. (i.e., the type of the struct)
    pub ty: &'ta HirTy<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExprArgument<'ta> {
    pub span: Span,
    pub field: HirName,
    pub expr: Box<HirExpr<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirGroupExpr<'ta> {
    pub span: Span,
    pub inner: Box<HirExpr<'ta>>,
    pub ty: &'ta HirTy<'ta>,
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
    Le,
    Ge,
    Lte,
    Gte,
    And,
    Or,
}
