use crate::Span;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct TranslationUnit {
    pub items: Vec<Box<Item>>,
}

/// An item in the translation unit.
///
/// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
/// currently means either functions or types.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum Item {
    Function(Box<FunctionItem>),
    Type(Box<TypeItem>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct FunctionItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub parameters: Vec<Box<FunctionParameterItem>>,
    pub return_type: Option<Box<Type>>,
    pub body: Vec<Box<Stmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct FunctionParameterItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Box<Type>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct TypeItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub members: Vec<Box<TypeMemberItem>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct TypeMemberItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Box<Type>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum Stmt {
    Let(Box<LetStmt>),
    Return(Box<ReturnStmt>),
    For(Box<ForStmt>),
    Break(Box<BreakStmt>),
    Continue(Box<ContinueStmt>),
    If(Box<IfStmt>),
    Expr(Box<ExprStmt>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct LetStmt {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Option<Box<Type>>,
    pub value: Box<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ReturnStmt {
    pub span: Span,
    pub value: Option<Box<Expr>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ForStmt {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Box<Type>,
    pub initializer: Box<Expr>,
    pub condition: Box<Expr>,
    pub increment: Box<Expr>,
    pub body: Vec<Box<Stmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct BreakStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ContinueStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct IfStmt {
    pub span: Span,
    pub condition: Box<Expr>,
    pub happy_path: Vec<Box<Stmt>>,
    pub unhappy_path: Option<Vec<Box<Stmt>>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ExprStmt {
    pub span: Span,
    pub expr: Box<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum Expr {
    Assign(Box<AssignExpr>),
    BinaryOp(Box<BinaryOpExpr>),
    UnaryOp(Box<UnaryOpExpr>),
    Literal(Box<LiteralExpr>),
    DotIndex(Box<DotIndexExpr>),
    BracketIndex(Box<BracketIndexExpr>),
    Reference(Box<ReferenceExpr>),
    Call(Box<CallExpr>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct AssignExpr {
    pub span: Span,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct BinaryOpExpr {
    pub span: Span,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: BinaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct UnaryOpExpr {
    pub span: Span,
    pub operand: Box<Expr>,
    pub op: UnaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct LiteralExpr {
    pub span: Span,
    pub value: i32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct DotIndexExpr {
    pub span: Span,
    pub origin: Box<Expr>,
    pub index: Box<Identifier>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct BracketIndexExpr {
    pub span: Span,
    pub origin: Box<Expr>,
    pub index: Box<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ReferenceExpr {
    pub span: Span,
    pub name: Box<Identifier>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct CallExpr {
    pub span: Span,
    pub callee: Box<Expr>,
    pub arguments: Vec<Box<Expr>>,
}

/// An identifier.
///
/// This is practically a copy of the `TokenType::Identifier` variant, but we want to be able to
/// extract them from the AST, as we don't care for storing token types in the AST.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct Identifier {
    pub name: String,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum Type {
    Unit(Box<UnitType>),
    Integer32(Box<Integer32Type>),
    Pointer(Box<PointerType>),
    Named(Box<NamedType>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct UnitType {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct Integer32Type {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct PointerType {
    pub span: Span,
    pub inner: Box<Type>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct NamedType {
    pub span: Span,
    pub name: Box<Identifier>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum BinaryOp {
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
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub enum UnaryOp {
    Not,
    Neg,
}
