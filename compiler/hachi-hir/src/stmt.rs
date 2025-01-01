use crate::expr::HirExpr;
use crate::ty::HirTy;
use crate::HirName;
use hachi_syntax::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum HirStmt {
    Let(HirLetStmt),
    Loop(HirLoopStmt),
    Expr(HirExprStmt),
    Return(HirReturnStmt),
    If(HirIfStmt),
    Break(HirBreakStmt),
    Continue(HirContinueStmt),
    Block(HirBlockStmt),
}

impl HirStmt {
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
pub struct HirLetStmt {
    pub span: Span,
    pub name: HirName,
    pub r#type: Box<HirTy>,
    pub value: Box<HirExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirIfStmt {
    pub span: Span,
    pub condition: Box<HirExpr>,
    pub happy_path: Vec<Box<HirStmt>>,
    pub unhappy_path: Vec<Box<HirStmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirExprStmt {
    pub span: Span,
    pub expr: Box<HirExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirLoopStmt {
    pub span: Span,
    /// The condition for the loop to continue.
    ///
    /// For infinite loops, this node should be a constant literal of boolean true.
    pub condition: Box<HirExpr>,
    pub body: Vec<Box<HirStmt>>,
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
pub struct HirReturnStmt {
    pub span: Span,
    pub value: Option<Box<HirExpr>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct HirBlockStmt {
    pub span: Span,
    pub body: Vec<Box<HirStmt>>,
}
