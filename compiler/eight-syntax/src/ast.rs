use eight_span::Span;

/// The top-level AST node representing a single translation unit.
///
/// The term translation unit is used here to refer to a single source file.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTranslationUnit {
    pub items: Vec<AstItem>,
}

/// An item in the translation unit.
///
/// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
/// currently means either functions or types.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstItem {
    Function(AstFunctionItem),
    IntrinsicFunction(AstIntrinsicFunctionItem),
    IntrinsicScalar(AstIntrinsicScalarItem),
    Type(AstTypeItem),
}

impl AstItem {
    pub fn span(&self) -> &Span {
        match self {
            AstItem::Function(f) => &f.span,
            AstItem::IntrinsicFunction(f) => &f.span,
            AstItem::IntrinsicScalar(f) => &f.span,
            AstItem::Type(f) => &f.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstFunctionItem {
    pub span: Span,
    pub name: AstIdentifier,
    pub parameters: Vec<AstFunctionParameterItem>,
    pub type_parameters: Vec<AstFunctionTypeParameterItem>,
    pub return_type: Option<AstType>,
    pub body: Vec<AstStmt>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIntrinsicFunctionItem {
    pub span: Span,
    pub name: AstIdentifier,
    pub parameters: Vec<AstFunctionParameterItem>,
    pub type_parameters: Vec<AstFunctionTypeParameterItem>,
    pub return_type: AstType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstFunctionTypeParameterItem {
    pub span: Span,
    pub name: AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstFunctionParameterItem {
    pub span: Span,
    pub name: AstIdentifier,
    pub ty: AstType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIntrinsicScalarItem {
    pub span: Span,
    pub name: AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTypeItem {
    pub span: Span,
    pub name: AstIdentifier,
    pub members: Vec<AstTypeMemberItem>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTypeMemberItem {
    pub span: Span,
    pub name: AstIdentifier,
    pub ty: AstType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstStmt {
    Let(AstLetStmt),
    Return(AstReturnStmt),
    For(AstForStmt),
    Break(AstBreakStmt),
    Continue(AstContinueStmt),
    If(AstIfStmt),
    Expr(AstExprStmt),
}

impl AstStmt {
    /// Get the span of the inner statement.
    pub fn span(&self) -> &Span {
        match self {
            AstStmt::Let(s) => &s.span,
            AstStmt::Return(s) => &s.span,
            AstStmt::For(s) => &s.span,
            AstStmt::Break(s) => &s.span,
            AstStmt::Continue(s) => &s.span,
            AstStmt::If(s) => &s.span,
            AstStmt::Expr(s) => &s.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstLetStmt {
    pub span: Span,
    pub name: AstIdentifier,
    pub ty: Option<AstType>,
    pub value: AstExpr,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstReturnStmt {
    pub span: Span,
    pub value: Option<AstExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstForStmt {
    pub span: Span,
    pub initializer: Option<AstForStmtInitializer>,
    pub condition: Option<AstExpr>,
    pub increment: Option<AstExpr>,
    pub body: Vec<AstStmt>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstForStmtInitializer {
    pub span: Span,
    pub name: AstIdentifier,
    pub initializer: AstExpr,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBreakStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstContinueStmt {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIfStmt {
    pub span: Span,
    pub condition: AstExpr,
    pub happy_path: Vec<AstStmt>,
    pub unhappy_path: Option<Vec<AstStmt>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstExprStmt {
    pub span: Span,
    pub expr: AstExpr,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstExpr {
    Assign(AstAssignExpr),
    BinaryOp(AstBinaryOpExpr),
    UnaryOp(AstUnaryOpExpr),
    IntegerLiteral(AstIntegerLiteralExpr),
    BooleanLiteral(AstBooleanLiteralExpr),
    DotIndex(AstDotIndexExpr),
    BracketIndex(AstBracketIndexExpr),
    Reference(AstReferenceExpr),
    Call(AstCallExpr),
    Construct(AstConstructExpr),
    Group(AstGroupExpr),
}

impl AstExpr {
    /// Get the span of the inner expression.
    pub fn span(&self) -> &Span {
        match self {
            AstExpr::Assign(e) => &e.span,
            AstExpr::BinaryOp(e) => &e.span,
            AstExpr::UnaryOp(e) => &e.span,
            AstExpr::IntegerLiteral(e) => &e.span,
            AstExpr::BooleanLiteral(e) => &e.span,
            AstExpr::DotIndex(e) => &e.span,
            AstExpr::BracketIndex(e) => &e.span,
            AstExpr::Reference(e) => &e.span,
            AstExpr::Call(e) => &e.span,
            AstExpr::Construct(e) => &e.span,
            AstExpr::Group(e) => &e.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstAssignExpr {
    pub span: Span,
    pub lhs: Box<AstExpr>,
    pub rhs: Box<AstExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBinaryOpExpr {
    pub span: Span,
    pub lhs: Box<AstExpr>,
    pub rhs: Box<AstExpr>,
    pub op: AstBinaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstUnaryOpExpr {
    pub span: Span,
    pub operand: Box<AstExpr>,
    pub op: AstUnaryOp,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIntegerLiteralExpr {
    pub span: Span,
    pub value: i32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBooleanLiteralExpr {
    pub span: Span,
    pub value: bool,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstDotIndexExpr {
    pub span: Span,
    pub origin: Box<AstExpr>,
    pub index: AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBracketIndexExpr {
    pub span: Span,
    pub origin: Box<AstExpr>,
    pub index: Box<AstExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstReferenceExpr {
    pub span: Span,
    pub name: AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstCallExpr {
    pub span: Span,
    pub callee: Box<AstExpr>,
    pub arguments: Vec<AstExpr>,
    pub type_arguments: Vec<AstType>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstConstructExpr {
    pub span: Span,
    pub callee: AstType,
    pub arguments: Vec<AstConstructorExprArgument>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstConstructorExprArgument {
    pub span: Span,
    pub field: AstIdentifier,
    pub expr: AstExpr,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstGroupExpr {
    pub span: Span,
    pub inner: Box<AstExpr>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
/// An identifier.
///
/// This is practically a copy of the `TokenType::Identifier` variant, but we want to be able to
/// extract them from the AST, as we don't care for storing token types in the AST.
pub struct AstIdentifier {
    pub name: String,
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstType {
    Unit(AstUnitType),
    Integer32(AstInteger32Type),
    Pointer(AstPointerType),
    Named(AstNamedType),
    Boolean(AstBooleanType),
}

impl AstType {
    /// Get the span of the inner type.
    pub fn span(&self) -> &Span {
        match self {
            AstType::Unit(t) => &t.span,
            AstType::Integer32(t) => &t.span,
            AstType::Pointer(t) => &t.span,
            AstType::Named(t) => &t.span,
            AstType::Boolean(t) => &t.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstUnitType {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstInteger32Type {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBooleanType {
    pub span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstPointerType {
    pub span: Span,
    pub inner: Box<AstType>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstNamedType {
    pub span: Span,
    pub name: AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum AstBinaryOp {
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

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum AstUnaryOp {
    Not,
    Neg,
    Deref,
    AddressOf,
}
