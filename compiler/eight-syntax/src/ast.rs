use eight_span::Span;

/// The top-level AST node representing a single translation unit.
///
/// The term translation unit is used here to refer to a single source file.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTranslationUnit<'ast> {
    pub items: &'ast [&'ast AstItem<'ast>],
}

/// An item in the translation unit.
///
/// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
/// currently means either functions or types.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstItem<'ast> {
    Function(AstFunctionItem<'ast>),
    IntrinsicFunction(AstIntrinsicFunctionItem<'ast>),
    IntrinsicType(AstIntrinsicTypeItem<'ast>),
    Struct(AstStructItem<'ast>),
    Trait(AstTraitItem<'ast>),
    Instance(AstInstanceItem<'ast>),
}

impl<'ast> AstItem<'ast> {
    pub fn span(&self) -> &Span {
        match self {
            AstItem::Function(f) => &f.span,
            AstItem::IntrinsicFunction(f) => &f.span,
            AstItem::IntrinsicType(f) => &f.span,
            AstItem::Struct(f) => &f.span,
            AstItem::Trait(f) => &f.span,
            AstItem::Instance(f) => &f.span,
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstFunctionItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub parameters: &'ast [&'ast AstFunctionParameterItem<'ast>],
    pub type_parameters: &'ast [&'ast AstTypeParameterItem<'ast>],
    pub return_type: Option<&'ast AstType<'ast>>,
    pub body: &'ast [&'ast AstStmt<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIntrinsicFunctionItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub parameters: &'ast [&'ast AstFunctionParameterItem<'ast>],
    pub type_parameters: &'ast [&'ast AstTypeParameterItem<'ast>],
    pub return_type: &'ast AstType<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTypeParameterItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstFunctionParameterItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub ty: &'ast AstType<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstIntrinsicTypeItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstStructItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub members: &'ast [&'ast AstStructMemberItem<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstStructMemberItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub ty: &'ast AstType<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTraitItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub type_parameters: &'ast [&'ast AstTypeParameterItem<'ast>],
    pub members: &'ast [&'ast AstTraitFunctionItem<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstTraitFunctionItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub type_parameters: &'ast [&'ast AstTypeParameterItem<'ast>],
    pub parameters: &'ast [&'ast AstFunctionParameterItem<'ast>],
    pub return_type: Option<&'ast AstType<'ast>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstInstanceItem<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    /// The type parameters the trait instance is for
    pub instantiation_type_parameters: &'ast [&'ast AstType<'ast>],
    pub members: &'ast [&'ast AstFunctionItem<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstStmt<'ast> {
    Let(AstLetStmt<'ast>),
    Return(AstReturnStmt<'ast>),
    For(AstForStmt<'ast>),
    Break(AstBreakStmt),
    Continue(AstContinueStmt),
    If(AstIfStmt<'ast>),
    Expr(AstExprStmt<'ast>),
}

impl<'ast> AstStmt<'ast> {
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
pub struct AstLetStmt<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub ty: Option<&'ast AstType<'ast>>,
    pub value: &'ast AstExpr<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstReturnStmt<'ast> {
    pub span: Span,
    pub value: Option<&'ast AstExpr<'ast>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstForStmt<'ast> {
    pub span: Span,
    pub initializer: Option<&'ast AstForStmtInitializer<'ast>>,
    pub condition: Option<&'ast AstExpr<'ast>>,
    pub increment: Option<&'ast AstExpr<'ast>>,
    pub body: &'ast [&'ast AstStmt<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstForStmtInitializer<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
    pub initializer: &'ast AstExpr<'ast>,
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
pub struct AstIfStmt<'ast> {
    pub span: Span,
    pub condition: &'ast AstExpr<'ast>,
    pub happy_path: &'ast [&'ast AstStmt<'ast>],
    pub unhappy_path: Option<&'ast [&'ast AstStmt<'ast>]>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstExprStmt<'ast> {
    pub span: Span,
    pub expr: &'ast AstExpr<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum AstExpr<'ast> {
    Assign(AstAssignExpr<'ast>),
    BinaryOp(AstBinaryOpExpr<'ast>),
    UnaryOp(AstUnaryOpExpr<'ast>),
    IntegerLiteral(AstIntegerLiteralExpr),
    BooleanLiteral(AstBooleanLiteralExpr),
    DotIndex(AstDotIndexExpr<'ast>),
    BracketIndex(AstBracketIndexExpr<'ast>),
    Reference(AstReferenceExpr<'ast>),
    Call(AstCallExpr<'ast>),
    Construct(AstConstructExpr<'ast>),
    Group(AstGroupExpr<'ast>),
}

impl<'ast> AstExpr<'ast> {
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
pub struct AstAssignExpr<'ast> {
    pub span: Span,
    pub lhs: &'ast AstExpr<'ast>,
    pub rhs: &'ast AstExpr<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBinaryOpExpr<'ast> {
    pub span: Span,
    pub lhs: &'ast AstExpr<'ast>,
    pub rhs: &'ast AstExpr<'ast>,
    pub op: AstBinaryOp,
    pub op_span: Span,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstUnaryOpExpr<'ast> {
    pub span: Span,
    pub operand: &'ast AstExpr<'ast>,
    pub op: AstUnaryOp,
    pub op_span: Span,
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
pub struct AstDotIndexExpr<'ast> {
    pub span: Span,
    pub origin: &'ast AstExpr<'ast>,
    pub index: &'ast AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstBracketIndexExpr<'ast> {
    pub span: Span,
    pub origin: &'ast AstExpr<'ast>,
    pub index: &'ast AstExpr<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstReferenceExpr<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstCallExpr<'ast> {
    pub span: Span,
    pub callee: &'ast AstExpr<'ast>,
    pub arguments: &'ast [&'ast AstExpr<'ast>],
    pub type_arguments: &'ast [&'ast AstType<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstConstructExpr<'ast> {
    pub span: Span,
    pub callee: &'ast AstType<'ast>,
    pub arguments: &'ast [&'ast AstConstructorExprArgument<'ast>],
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstConstructorExprArgument<'ast> {
    pub span: Span,
    pub field: &'ast AstIdentifier,
    pub expr: &'ast AstExpr<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstGroupExpr<'ast> {
    pub span: Span,
    pub inner: &'ast AstExpr<'ast>,
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
pub enum AstType<'ast> {
    Unit(AstUnitType),
    Integer32(AstInteger32Type),
    Pointer(AstPointerType<'ast>),
    Named(AstNamedType<'ast>),
    Boolean(AstBooleanType),
}

impl<'ast> AstType<'ast> {
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
pub struct AstPointerType<'ast> {
    pub span: Span,
    pub inner: &'ast AstType<'ast>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct AstNamedType<'ast> {
    pub span: Span,
    pub name: &'ast AstIdentifier,
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
