use crate::ty::HirTy;
use hachi_syntax::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirExpr<'hir> {
    IntegerLiteral(HirIntegerLiteralExpr<'hir>),
    BooleanLiteral(HirBooleanLiteralExpr<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirIntegerLiteralExpr<'hir> {
    span: Span,
    value: i32,
    ty: &'hir HirTy<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirBooleanLiteralExpr<'hir> {
    span: Span,
    value: bool,
    ty: &'hir HirTy<'hir>,
}
