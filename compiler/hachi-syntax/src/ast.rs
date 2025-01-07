use crate::{declare_ast_node, declare_ast_variant};
use hachi_span::Span;

declare_ast_node! {
    /// The top-level AST node representing a single translation unit.
    ///
    /// The term translation unit is used here to refer to a single source file.
    pub struct TranslationUnit {
        span: Span,
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
    }
}

declare_ast_node! {
    pub struct FunctionItem {
        span: Span,
        pub name: Box<Identifier>,
        pub parameters: Vec<Box<FunctionParameterItem>>,
        pub type_parameters: Vec<Box<FunctionTypeParameterItem>>,
        pub return_type: Option<Box<Type>>,
        pub body: Vec<Box<Stmt>>,
    }
}

declare_ast_node! {
    pub struct IntrinsicFunctionItem {
        span: Span,
        pub name: Box<Identifier>,
        pub parameters: Vec<Box<FunctionParameterItem>>,
        pub type_parameters: Vec<Box<FunctionTypeParameterItem>>,
        pub return_type: Box<Type>,
    }
}

declare_ast_node! {
    pub struct FunctionTypeParameterItem {
        span: Span,
        pub name: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct FunctionParameterItem {
        span: Span,
        pub name: Box<Identifier>,
        pub r#type: Box<Type>,
    }
}

declare_ast_node! {
    pub struct TypeItem {
        span: Span,
        pub name: Box<Identifier>,
        pub members: Vec<Box<TypeMemberItem>>,
    }
}

declare_ast_node! {
    pub struct TypeMemberItem {
        span: Span,
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
        span: Span,
        pub name: Box<Identifier>,
        pub r#type: Option<Box<Type>>,
        pub value: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct ReturnStmt {
        span: Span,
        pub value: Option<Box<Expr>>,
    }
}

declare_ast_node! {
    pub struct ForStmt {
        span: Span,
        pub initializer: Option<Box<ForStmtInitializer>>,
        pub condition: Option<Box<Expr>>,
        pub increment: Option<Box<Expr>>,
        pub body: Vec<Box<Stmt>>,
    }
}

declare_ast_node! {
    pub struct ForStmtInitializer {
        span: Span,
        pub name: Box<Identifier>,
        pub initializer: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct BreakStmt {
        span: Span,
    }
}

declare_ast_node! {
    pub struct ContinueStmt {
        span: Span,
    }
}

declare_ast_node! {
    pub struct IfStmt {
        span: Span,
        pub condition: Box<Expr>,
        pub happy_path: Vec<Box<Stmt>>,
        pub unhappy_path: Option<Vec<Box<Stmt>>>,
    }
}

declare_ast_node! {
    pub struct ExprStmt {
        span: Span,
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
        span: Span,
        pub lhs: Box<Expr>,
        pub rhs: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct BinaryOpExpr {
        span: Span,
        pub lhs: Box<Expr>,
        pub rhs: Box<Expr>,
        pub op: BinaryOp,
    }
}

declare_ast_node! {
    pub struct UnaryOpExpr {
        span: Span,
        pub operand: Box<Expr>,
        pub op: UnaryOp,
    }
}

declare_ast_node! {
    pub struct IntegerLiteralExpr {
        span: Span,
        pub value: i32,
    }
}

declare_ast_node! {
    pub struct BooleanLiteralExpr {
        span: Span,
        pub value: bool,
    }
}

declare_ast_node! {
    pub struct DotIndexExpr {
        span: Span,
        pub origin: Box<Expr>,
        pub index: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct BracketIndexExpr {
        span: Span,
        pub origin: Box<Expr>,
        pub index: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct ReferenceExpr {
        span: Span,
        pub name: Box<Identifier>,
    }
}

declare_ast_node! {
    pub struct CallExpr {
        span: Span,
        pub callee: Box<Expr>,
        pub arguments: Vec<Box<Expr>>,
        pub type_arguments: Vec<Box<Type>>,
    }
}

declare_ast_node! {
    pub struct ConstructExpr {
        span: Span,
        pub callee: Box<Type>,
        pub arguments: Vec<Box<ConstructorExprArgument>>,
    }
}

declare_ast_node! {
    pub struct ConstructorExprArgument {
        span: Span,
        pub field: Box<Identifier>,
        pub expr: Box<Expr>,
    }
}

declare_ast_node! {
    pub struct GroupExpr {
        span: Span,
        pub inner: Box<Expr>,
    }
}

declare_ast_node! {
    /// An identifier.
    ///
    /// This is practically a copy of the `TokenType::Identifier` variant, but we want to be able to
    /// extract them from the AST, as we don't care for storing token types in the AST.
    pub struct Identifier {
        pub name: String,
        span: Span,
    }
}

declare_ast_variant! {
    pub enum Type {
        Unit(Box<UnitType>),
        Integer32(Box<Integer32Type>),
        Pointer(Box<PointerType>),
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
            Type::Named(t) => &t.span,
            Type::Boolean(t) => &t.span,
        }
    }
}

declare_ast_node! {
    pub struct UnitType {
        span: Span,
    }
}

declare_ast_node! {
    pub struct Integer32Type {
        span: Span,
    }
}

declare_ast_node! {
    pub struct BooleanType {
        span: Span,
    }
}

declare_ast_node! {
    pub struct PointerType {
        span: Span,
        pub inner: Box<Type>,
    }
}

declare_ast_node! {
    pub struct NamedType {
        span: Span,
        pub name: Box<Identifier>,
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
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

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
    Deref,
    AddressOf,
}
