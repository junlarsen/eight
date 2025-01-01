use crate::InternedTy;
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
