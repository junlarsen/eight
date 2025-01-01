use crate::InternedTy;
use hachi_syntax::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirExpr<'hir> {
    IntegerLiteral(HirIntegerLiteralExpr<'hir>),
    BooleanLiteral(HirBooleanLiteralExpr<'hir>),
    Assign(HirAssignExpr<'hir>),
    UnaryOp(HirUnaryOpExpr<'hir>),
    BinaryOp(HirBinaryOpExpr<'hir>),
    AddressOf(HirAddressOfExpr<'hir>),
    Deref(HirDerefExpr<'hir>),
    ConstantIndex(HirConstantIndexExpr<'hir>),
    OffsetIndex(HirOffsetIndexExpr<'hir>),
    Call(HirCallExpr<'hir>),
    Construct(HirConstructExpr<'hir>),
    Group(HirGroupExpr<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirIntegerLiteralExpr<'hir> {
    pub span: Span,
    pub value: i32,
    pub ty: InternedTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirBooleanLiteralExpr<'hir> {
    pub span: Span,
    pub value: bool,
    pub ty: InternedTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirAssignExpr<'hir> {
    pub span: Span,
    pub lhs: HirExpr<'hir>,
    pub rhs: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirUnaryOpExpr<'hir> {
    pub span: Span,
    pub operand: HirExpr<'hir>,
    pub op: HirUnaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirBinaryOpExpr<'hir> {
    pub span: Span,
    pub lhs: HirExpr<'hir>,
    pub rhs: HirExpr<'hir>,
    pub op: HirBinaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirAddressOfExpr<'hir> {
    pub span: Span,
    pub inner: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirDerefExpr<'hir> {
    pub span: Span,
    pub inner: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirConstantIndexExpr<'hir> {
    pub span: Span,
    pub origin: HirExpr<'hir>,
    pub index: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirOffsetIndexExpr<'hir> {
    pub span: Span,
    pub origin: HirExpr<'hir>,
    pub index: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirCallExpr<'hir> {
    pub span: Span,
    pub callee: HirExpr<'hir>,
    pub arguments: Vec<HirExpr<'hir>>,
    pub type_arguments: Vec<InternedTy<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirConstructExpr<'hir> {
    pub span: Span,
    pub callee: InternedTy<'hir>,
    pub arguments: Vec<HirExpr<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirGroupExpr<'hir> {
    pub span: Span,
    pub inner: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirUnaryOp {
    Not,
    Neg,
    Deref,
    AddressOf,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
