use crate::expr::HirExpr;
use crate::{HirName, InternedTy};
use hachi_syntax::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum HirStmt<'hir> {
    Let(HirLetStmt<'hir>),
    Loop(HirLoopStmt<'hir>),
    Expr(HirExprStmt<'hir>),
    Return(HirReturnStmt<'hir>),
    If(HirIfStmt<'hir>),
    Break(HirBreakStmt<'hir>),
    Continue(HirContinueStmt<'hir>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirLetStmt<'hir> {
    pub span: Span,
    pub name: HirName<'hir>,
    pub r#type: InternedTy<'hir>,
    pub value: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirIfStmt<'hir> {
    pub span: Span,
    pub condition: HirExpr<'hir>,
    pub happy_path: Vec<HirStmt<'hir>>,
    pub unhappy_path: Vec<HirStmt<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirExprStmt<'hir> {
    pub span: Span,
    pub expr: HirExpr<'hir>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirLoopStmt<'hir> {
    pub span: Span,
    /// The initializer for the loop, if any.
    ///
    /// TODO: Consider if this should not be lowered into a let statement
    pub initializer: Option<HirLetStmt<'hir>>,
    /// The condition for the loop to continue.
    ///
    /// For infinite loops, this node should be a constant literal of boolean true.
    pub condition: HirExpr<'hir>,
    pub body: Vec<HirStmt<'hir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirBreakStmt<'hir> {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirContinueStmt<'hir> {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct HirReturnStmt<'hir> {
    pub span: Span,
    pub value: Option<HirExpr<'hir>>,
}
