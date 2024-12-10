use crate::Span;

#[derive(Debug)]
pub struct TranslationUnit {
    pub items: Vec<Box<Item>>,
}

/// An item in the translation unit.
///
/// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
/// currently means either functions or types.
#[derive(Debug)]
pub enum Item {
    Function(Box<FunctionItem>),
    Type(Box<TypeItem>),
}

#[derive(Debug)]
pub struct FunctionItem {
    pub span: Span,
    pub parameters: Vec<Box<Type>>,
    pub arguments: Vec<Box<Identifier>>,
    pub return_type: Option<Box<Type>>,
    pub body: Vec<Box<Stmt>>,
}

#[derive(Debug)]
pub struct TypeItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub members: Vec<Box<TypeMemberItem>>,
}

#[derive(Debug)]
pub struct TypeMemberItem {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Box<Type>,
}

#[derive(Debug)]
pub enum Stmt {
    Let(Box<LetStmt>),
    Return(Box<ReturnStmt>),
    For(Box<ForStmt>),
    Break(Box<BreakStmt>),
    Continue(Box<ContinueStmt>),
    If(Box<IfStmt>),
}

#[derive(Debug)]
pub struct LetStmt {
    pub span: Span,
    pub name: Box<Identifier>,
    pub r#type: Option<Box<Type>>,
    pub value: Box<Expr>,
}

#[derive(Debug)]
pub struct ReturnStmt {
    pub span: Span,
    pub value: Option<Box<Expr>>,
}

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

#[derive(Debug)]
pub struct BreakStmt {
    pub span: Span,
}

#[derive(Debug)]
pub struct ContinueStmt {
    pub span: Span,
}

#[derive(Debug)]
pub struct IfStmt {
    pub span: Span,
    pub condition: Box<Expr>,
    pub happy_path: Vec<Box<Stmt>>,
    pub unhappy_path: Option<Vec<Box<Stmt>>>,
}

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

#[derive(Debug)]
pub struct AssignExpr {
    pub span: Span,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[derive(Debug)]
pub struct BinaryOpExpr {
    pub span: Span,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
    pub op: BinaryOp,
}

#[derive(Debug)]
pub struct UnaryOpExpr {
    pub span: Span,
    pub operand: Box<Expr>,
    pub op: UnaryOp,
}

#[derive(Debug)]
pub struct LiteralExpr {
    pub span: Span,
    pub value: i32,
}

#[derive(Debug)]
pub struct DotIndexExpr {
    pub span: Span,
    pub origin: Box<Expr>,
    pub index: Box<Identifier>,
}

#[derive(Debug)]
pub struct BracketIndexExpr {
    pub span: Span,
    pub origin: Box<Expr>,
    pub index: Box<Expr>,
}

#[derive(Debug)]
pub struct ReferenceExpr {
    pub span: Span,
    pub name: Box<Identifier>,
}

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
#[derive(Debug)]
pub struct Identifier {
    pub span: Span,
}

#[derive(Debug)]
pub enum Type {
    /// The unit type, implying that no value is returned from a function.
    ///
    /// This type can only be used to mark the return types.
    Unit { span: Span },
    /// The builtin i32 integer type.
    Integer32 { span: Span },
    /// A pointer type to an inner value.
    Pointer { span: Span, inner: Box<Type> },
}

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

#[derive(Debug)]
pub enum UnaryOp {
    Not,
    Neg,
}
