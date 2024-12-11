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

impl Stmt {
    /// Get the span of the inner statement.
    pub fn span(&self) -> &Span {
        match self {
            Stmt::Let(s) => &s.span,
            Stmt::Return(s) => &s.span,
            Stmt::For(s) => &s.span,
            Stmt::Break(s) => &s.span,
            Stmt::Continue(s) => &s.span,
            Stmt::If(s) => &s.span,
            Stmt::Expr(s) => &s.span,
        }
    }
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
    pub initializer: Option<Box<ForStmtInitializer>>,
    pub condition: Option<Box<Expr>>,
    pub increment: Option<Box<Expr>>,
    pub body: Vec<Box<Stmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ForStmtInitializer {
    pub span: Span,
    pub name: Box<Identifier>,
    pub initializer: Box<Expr>,
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
    IntegerLiteral(Box<IntegerLiteralExpr>),
    DotIndex(Box<DotIndexExpr>),
    BracketIndex(Box<BracketIndexExpr>),
    Reference(Box<ReferenceExpr>),
    Call(Box<CallExpr>),
    Construct(Box<ConstructExpr>),
    Group(Box<GroupExpr>),
}

impl Expr {
    /// Get the span of the inner expression.
    pub fn span(&self) -> &Span {
        match self {
            Expr::Assign(e) => &e.span,
            Expr::BinaryOp(e) => &e.span,
            Expr::UnaryOp(e) => &e.span,
            Expr::IntegerLiteral(e) => &e.span,
            Expr::DotIndex(e) => &e.span,
            Expr::BracketIndex(e) => &e.span,
            Expr::Reference(e) => &e.span,
            Expr::Call(e) => &e.span,
            Expr::Construct(e) => &e.span,
            Expr::Group(e) => &e.span,
        }
    }
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
pub struct IntegerLiteralExpr {
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

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ConstructExpr {
    pub span: Span,
    pub callee: Box<Expr>,
    pub arguments: Vec<Box<ConstructorExprArgument>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct ConstructorExprArgument {
    pub span: Span,
    pub field: Box<Identifier>,
    pub expr: Box<Expr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
pub struct GroupExpr {
    pub span: Span,
    pub inner: Box<Expr>,
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

impl Type {
    /// Get the span of the inner type.
    pub fn span(&self) -> &Span {
        match self {
            Type::Unit(t) => &t.span,
            Type::Integer32(t) => &t.span,
            Type::Pointer(t) => &t.span,
            Type::Named(t) => &t.span,
        }
    }
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
#[derive(Debug, PartialEq, Eq)]
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
    Lte,
    Gte,
    And,
    Or,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
    Deref,
    AddressOf,
}
