use crate::expr::HirExpr;
use crate::ty::HirTy;
use eight_span::Span;

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
    pub fn span(&self) -> &Span {
        match self {
            HirStmt::Let(s) => &s.span,
            HirStmt::Loop(s) => &s.span,
            HirStmt::Expr(s) => &s.span,
            HirStmt::Return(s) => &s.span,
            HirStmt::If(s) => &s.span,
            HirStmt::Break(s) => &s.span,
            HirStmt::Continue(s) => &s.span,
            HirStmt::Block(s) => &s.span,
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
    pub body: Vec<Box<HirStmt<'hir>>>,
}
