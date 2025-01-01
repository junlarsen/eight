use crate::expr::HirExpr;
use crate::HirName;
use hachi_syntax::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirStmt<'hir> {
    Let(HirLetStmt<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirLetStmt<'hir> {
    pub span: Span,
    pub name: HirName<'hir>,
    pub r#type: InternedTy<'hir>,
    pub value: HirExpr<'hir>,
}
