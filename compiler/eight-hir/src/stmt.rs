use crate::expr::HirExpr;
use crate::ty::HirTy;
use crate::HirName;
use eight_span::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirStmt<'ta> {
    Let(HirLetStmt<'ta>),
    Loop(HirLoopStmt<'ta>),
    Expr(HirExprStmt<'ta>),
    Return(HirReturnStmt<'ta>),
    If(HirIfStmt<'ta>),
    Break(HirBreakStmt),
    Continue(HirContinueStmt),
    Block(HirBlockStmt<'ta>),
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
pub struct HirLetStmt<'ta> {
    pub span: Span,
    pub name: HirName,
    pub r#type: &'ta HirTy<'ta>,
    pub type_annotation: Option<Span>,
    pub value: HirExpr<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIfStmt<'ta> {
    pub span: Span,
    pub condition: HirExpr<'ta>,
    pub happy_path: Vec<HirStmt<'ta>>,
    pub unhappy_path: Vec<HirStmt<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirExprStmt<'ta> {
    pub span: Span,
    pub expr: HirExpr<'ta>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirLoopStmt<'ta> {
    pub span: Span,
    /// The condition for the loop to continue.
    ///
    /// For infinite loops, this node should be a constant literal of boolean true.
    pub condition: HirExpr<'ta>,
    pub body: Vec<HirStmt<'ta>>,
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
pub struct HirReturnStmt<'ta> {
    pub span: Span,
    pub value: Option<HirExpr<'ta>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBlockStmt<'ta> {
    pub span: Span,
    pub body: Vec<Box<HirStmt<'ta>>>,
}
