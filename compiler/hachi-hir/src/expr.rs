use crate::ty::HirTy;
use crate::HirName;
use hachi_span::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirExpr {
    IntegerLiteral(HirIntegerLiteralExpr),
    BooleanLiteral(HirBooleanLiteralExpr),
    Assign(HirAssignExpr),
    UnaryOp(HirUnaryOpExpr),
    BinaryOp(HirBinaryOpExpr),
    Reference(HirReferenceExpr),
    ConstantIndex(HirConstantIndexExpr),
    OffsetIndex(HirOffsetIndexExpr),
    Call(HirCallExpr),
    Construct(HirConstructExpr),
    Group(HirGroupExpr),
    AddressOf(HirAddressOfExpr),
    Deref(HirDerefExpr),
}

impl HirExpr {
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

    pub fn ty(&self) -> &HirTy {
        match self {
            HirExpr::IntegerLiteral(e) => &e.ty,
            HirExpr::BooleanLiteral(e) => &e.ty,
            HirExpr::Assign(e) => &e.ty,
            HirExpr::UnaryOp(e) => &e.ty,
            HirExpr::BinaryOp(e) => &e.ty,
            HirExpr::ConstantIndex(e) => &e.ty,
            HirExpr::OffsetIndex(e) => &e.ty,
            HirExpr::Call(e) => &e.ty,
            HirExpr::Construct(e) => &e.ty,
            HirExpr::Group(e) => &e.ty,
            HirExpr::Reference(e) => &e.ty,
            HirExpr::AddressOf(e) => &e.ty,
            HirExpr::Deref(e) => &e.ty,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIntegerLiteralExpr {
    pub span: Span,
    pub value: i32,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBooleanLiteralExpr {
    pub span: Span,
    pub value: bool,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAssignExpr {
    pub span: Span,
    pub lhs: Box<HirExpr>,
    pub rhs: Box<HirExpr>,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirUnaryOpExpr {
    pub span: Span,
    pub operand: Box<HirExpr>,
    pub op: HirUnaryOp,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBinaryOpExpr {
    pub span: Span,
    pub lhs: Box<HirExpr>,
    pub rhs: Box<HirExpr>,
    pub op: HirBinaryOp,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirAddressOfExpr {
    pub span: Span,
    pub inner: Box<HirExpr>,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirDerefExpr {
    pub span: Span,
    pub inner: Box<HirExpr>,
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirReferenceExpr {
    pub span: Span,
    pub name: HirName,
    /// The type of `name` in the current scope.
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirOffsetIndexExpr {
    pub span: Span,
    pub origin: Box<HirExpr>,
    pub index: Box<HirExpr>,
    /// The type of the result of expression.
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstantIndexExpr {
    pub span: Span,
    pub origin: Box<HirExpr>,
    pub index: HirName,
    /// The type of the result of expression.
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirCallExpr {
    pub span: Span,
    pub callee: Box<HirExpr>,
    pub arguments: Vec<Box<HirExpr>>,
    pub type_arguments: Vec<Box<HirTy>>,
    /// The type of the result of the call expression.
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExpr {
    pub span: Span,
    pub callee: Box<HirTy>,
    pub arguments: Vec<Box<HirConstructExprArgument>>,
    /// The returned type of the construct expression. (i.e., the type of the struct)
    pub ty: Box<HirTy>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirConstructExprArgument {
    pub span: Span,
    pub field: HirName,
    pub expr: Box<HirExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirGroupExpr {
    pub span: Span,
    pub inner: Box<HirExpr>,
    pub ty: Box<HirTy>,
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
