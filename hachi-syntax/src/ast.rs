use crate::{declare_ast_node, declare_ast_variant, Span};

/// An internal ID for a single AST Node.
///
/// This ID is deterministically generated by the parser and is guaranteed to be unique
/// across a single translation unit.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq)]
pub struct NodeId(usize);

impl NodeId {
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    pub const fn id(&self) -> usize {
        self.0
    }
}

impl From<usize> for NodeId {
    fn from(id: usize) -> Self {
        Self::new(id)
    }
}

declare_ast_node! {
    /// The top-level AST node representing a single translation unit.
    ///
    /// The term translation unit is used here to refer to a single source file.
    pub struct TranslationUnit {
        id: NodeId,
        pub items: Vec<Box<Item>>,
    }
}

declare_ast_variant! {
    /// An item in the translation unit.
    ///
    /// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
    /// currently means either functions or types.
    pub enum Item {
        Function(Box<FunctionItem>),
        IntrinsicFunction(Box<IntrinsicFunctionItem>),
        Type(Box<TypeItem>),
        IntrinsicType(Box<IntrinsicTypeItem>),
    }
}

declare_ast_node! {
    pub struct FunctionItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub parameters: Vec<Box<FunctionParameterItem>>,
        pub type_parameters: Vec<Box<FunctionTypeParameterItem>>,
        pub return_type: Option<Box<Type>>,
        pub body: Vec<Box<Stmt>>,
    }
}

declare_ast_node! {
    pub struct IntrinsicFunctionItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub parameters: Vec<Box<FunctionParameterItem>>,
        pub type_parameters: Vec<Box<FunctionTypeParameterItem>>,
        pub return_type: Box<Type>,
    }
}

declare_ast_node! {
    pub struct FunctionTypeParameterItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct FunctionParameterItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub r#type: Box<Type>,
    }
}

declare_ast_node! {
    pub struct IntrinsicTypeItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct TypeItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub members: Vec<Box<TypeMemberItem>>,
    }
}

declare_ast_node! {
    pub struct TypeMemberItem {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub r#type: Box<Type>,
    }
}

declare_ast_variant! {
    pub enum Stmt {
        Let(Box<LetStmt>),
        Return(Box<ReturnStmt>),
        For(Box<ForStmt>),
        Break(Box<BreakStmt>),
        Continue(Box<ContinueStmt>),
        If(Box<IfStmt>),
        Expr(Box<ExprStmt>),
    }
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

declare_ast_node! {
    pub struct LetStmt {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub r#type: Option<Box<Type>>,
        pub value: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct ReturnStmt {
        id: NodeId,
        pub span: Span,
        pub value: Option<Box<Expr>>,
    }
}

declare_ast_node! {
    pub struct ForStmt {
        id: NodeId,
        pub span: Span,
        pub initializer: Option<Box<ForStmtInitializer>>,
        pub condition: Option<Box<Expr>>,
        pub increment: Option<Box<Expr>>,
        pub body: Vec<Box<Stmt>>,
    }
}

declare_ast_node! {
    pub struct ForStmtInitializer {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
        pub initializer: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct BreakStmt {
        id: NodeId,
        pub span: Span,
    }
}

declare_ast_node! {
    pub struct ContinueStmt {
        id: NodeId,
        pub span: Span,
    }
}

declare_ast_node! {
    pub struct IfStmt {
        id: NodeId,
        pub span: Span,
        pub condition: Box<Expr>,
        pub happy_path: Vec<Box<Stmt>>,
        pub unhappy_path: Option<Vec<Box<Stmt>>>,
    }
}

declare_ast_node! {
    pub struct ExprStmt {
        id: NodeId,
        pub span: Span,
        pub expr: Box<Expr>,
    }
}

declare_ast_variant! {
    pub enum Expr {
        Assign(Box<AssignExpr>),
        BinaryOp(Box<BinaryOpExpr>),
        UnaryOp(Box<UnaryOpExpr>),
        IntegerLiteral(Box<IntegerLiteralExpr>),
        BooleanLiteral(Box<BooleanLiteralExpr>),
        DotIndex(Box<DotIndexExpr>),
        BracketIndex(Box<BracketIndexExpr>),
        Reference(Box<ReferenceExpr>),
        Call(Box<CallExpr>),
        Construct(Box<ConstructExpr>),
        Group(Box<GroupExpr>),
    }
}

impl Expr {
    /// Get the span of the inner expression.
    pub fn span(&self) -> &Span {
        match self {
            Expr::Assign(e) => &e.span,
            Expr::BinaryOp(e) => &e.span,
            Expr::UnaryOp(e) => &e.span,
            Expr::IntegerLiteral(e) => &e.span,
            Expr::BooleanLiteral(e) => &e.span,
            Expr::DotIndex(e) => &e.span,
            Expr::BracketIndex(e) => &e.span,
            Expr::Reference(e) => &e.span,
            Expr::Call(e) => &e.span,
            Expr::Construct(e) => &e.span,
            Expr::Group(e) => &e.span,
        }
    }
}

declare_ast_node! {
    pub struct AssignExpr {
        id: NodeId,
        pub span: Span,
        pub lhs: Box<Expr>,
        pub rhs: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct BinaryOpExpr {
        id: NodeId,
        pub span: Span,
        pub lhs: Box<Expr>,
        pub rhs: Box<Expr>,
        pub op: BinaryOp,
    }
}

declare_ast_node! {
    pub struct UnaryOpExpr {
        id: NodeId,
        pub span: Span,
        pub operand: Box<Expr>,
        pub op: UnaryOp,
    }
}

declare_ast_node! {
    pub struct IntegerLiteralExpr {
        id: NodeId,
        pub span: Span,
        pub value: i32,
    }
}

declare_ast_node! {
    pub struct BooleanLiteralExpr {
        id: NodeId,
        pub span: Span,
        pub value: bool,
    }
}

declare_ast_node! {
    pub struct DotIndexExpr {
        id: NodeId,
        pub span: Span,
        pub origin: Box<Expr>,
        pub index: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct BracketIndexExpr {
        id: NodeId,
        pub span: Span,
        pub origin: Box<Expr>,
        pub index: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct ReferenceExpr {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct CallExpr {
        id: NodeId,
        pub span: Span,
        pub callee: Box<Expr>,
        pub arguments: Vec<Box<Expr>>,
        pub type_arguments: Vec<Box<Type>>,
    }
}

declare_ast_node! {
    pub struct ConstructExpr {
        id: NodeId,
        pub span: Span,
        pub callee: Box<Expr>,
        pub arguments: Vec<Box<ConstructorExprArgument>>,
    }
}

declare_ast_node! {
    pub struct ConstructorExprArgument {
        id: NodeId,
        pub span: Span,
        pub field: Box<Identifier>,
        pub expr: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct GroupExpr {
        id: NodeId,
        pub span: Span,
        pub inner: Box<Expr>,
    }
}

declare_ast_node! {
    /// An identifier.
    ///
    /// This is practically a copy of the `TokenType::Identifier` variant, but we want to be able to
    /// extract them from the AST, as we don't care for storing token types in the AST.
    pub struct Identifier {
        id: NodeId,
        pub name: String,
        pub span: Span,
    }
}

declare_ast_variant! {
    pub enum Type {
        Unit(Box<UnitType>),
        Integer32(Box<Integer32Type>),
        Pointer(Box<PointerType>),
        Reference(Box<ReferenceType>),
        Named(Box<NamedType>),
        Boolean(Box<BooleanType>),
    }
}

impl Type {
    /// Get the span of the inner type.
    pub fn span(&self) -> &Span {
        match self {
            Type::Unit(t) => &t.span,
            Type::Integer32(t) => &t.span,
            Type::Pointer(t) => &t.span,
            Type::Reference(t) => &t.span,
            Type::Named(t) => &t.span,
            Type::Boolean(t) => &t.span,
        }
    }
}

declare_ast_node! {
    pub struct UnitType {
        id: NodeId,
        pub span: Span,
    }
}

declare_ast_node! {
    pub struct Integer32Type {
        id: NodeId,
        pub span: Span,
    }
}

declare_ast_node! {
    pub struct BooleanType {
        id: NodeId,
        pub span: Span,
    }
}

declare_ast_node! {
    pub struct PointerType {
        id: NodeId,
        pub span: Span,
        pub inner: Box<Type>,
    }
}

declare_ast_node! {
    pub struct ReferenceType {
        id: NodeId,
        pub span: Span,
        pub inner: Box<Type>,
    }
}

declare_ast_node! {
    pub struct NamedType {
        id: NodeId,
        pub span: Span,
        pub name: Box<Identifier>,
    }
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
