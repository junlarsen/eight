use crate::ty::HirTy;
use eight_span::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirExpr<'hir> {
    IntegerLiteral(HirIntegerLiteralExpr<'hir>),
    BooleanLiteral(HirBooleanLiteralExpr<'hir>),
    Assign(HirAssignExpr<'hir>),
    UnaryOp(HirUnaryOpExpr<'hir>),
    BinaryOp(HirBinaryOpExpr<'hir>),
    Reference(HirReferenceExpr<'hir>),
    ConstantIndex(HirConstantIndexExpr<'hir>),
    OffsetIndex(HirOffsetIndexExpr<'hir>),
    Call(HirCallExpr<'hir>),
    Construct(HirConstructExpr<'hir>),
    Group(HirGroupExpr<'hir>),
    AddressOf(HirAddressOfExpr<'hir>),
    Deref(HirDerefExpr<'hir>),
}

impl<'hir> HirExpr<'hir> {
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
    pub arguments: Vec<Box<HirExpr<'hir>>>,
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
