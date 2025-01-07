use crate::{declare_ast_node, declare_ast_variant};
use hachi_span::Span;

declare_ast_node! {
    /// The top-level AST node representing a single translation unit.
    ///
    /// The term translation unit is used here to refer to a single source file.
    pub struct AstTranslationUnit {
        span: Span,
        pub items: Vec<AstItem>,
    }
}

declare_ast_variant! {
    /// An item in the translation unit.
    ///
    /// An `Item` is anything that can be declared at the top-level scope of a translation unit. This
    /// currently means either functions or types.
    pub enum AstItem {
        Function(AstFunctionItem),
        IntrinsicFunction(AstIntrinsicFunctionItem),
        Type(AstTypeItem),
    }
}

declare_ast_node! {
    pub struct AstFunctionItem {
        span: Span,
        pub name: AstIdentifier,
        pub parameters: Vec<AstFunctionParameterItem>,
        pub type_parameters: Vec<AstFunctionTypeParameterItem>,
        pub return_type: Option<AstType>,
        pub body: Vec<AstStmt>,
    }
}

declare_ast_node! {
    pub struct AstIntrinsicFunctionItem {
        span: Span,
        pub name: AstIdentifier,
        pub parameters: Vec<AstFunctionParameterItem>,
        pub type_parameters: Vec<AstFunctionTypeParameterItem>,
        pub return_type: AstType,
    }
}

declare_ast_node! {
    pub struct AstFunctionTypeParameterItem {
        span: Span,
        pub name: AstIdentifier,
    }
}

declare_ast_node! {
    pub struct AstFunctionParameterItem {
        span: Span,
        pub name: AstIdentifier,
        pub r#type: AstType,
    }
}

declare_ast_node! {
    pub struct AstTypeItem {
        span: Span,
        pub name: AstIdentifier,
        pub members: Vec<AstTypeMemberItem>,
    }
}

declare_ast_node! {
    pub struct AstTypeMemberItem {
        span: Span,
        pub name: AstIdentifier,
        pub r#type: AstType,
    }
}

declare_ast_variant! {
    pub enum AstStmt {
        Let(AstLetStmt),
        Return(AstReturnStmt),
        For(AstForStmt),
        Break(AstBreakStmt),
        Continue(AstContinueStmt),
        If(AstIfStmt),
        Expr(AstExprStmt),
    }
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

declare_ast_node! {
    pub struct AstLetStmt {
        span: Span,
        pub name: AstIdentifier,
        pub r#type: Option<AstType>,
        pub value: AstExpr,
    }
}

declare_ast_node! {
    pub struct AstReturnStmt {
        span: Span,
        pub value: Option<AstExpr>,
    }
}

declare_ast_node! {
    pub struct AstForStmt {
        span: Span,
        pub initializer: Option<AstForStmtInitializer>,
        pub condition: Option<AstExpr>,
        pub increment: Option<AstExpr>,
        pub body: Vec<AstStmt>,
    }
}

declare_ast_node! {
    pub struct AstForStmtInitializer {
        span: Span,
        pub name: AstIdentifier,
        pub initializer: AstExpr,
    }
}

declare_ast_node! {
    pub struct AstBreakStmt {
        span: Span,
    }
}

declare_ast_node! {
    pub struct AstContinueStmt {
        span: Span,
    }
}

declare_ast_node! {
    pub struct AstIfStmt {
        span: Span,
        pub condition: AstExpr,
        pub happy_path: Vec<AstStmt>,
        pub unhappy_path: Option<Vec<AstStmt >>,
    }
}

declare_ast_node! {
    pub struct AstExprStmt {
        span: Span,
        pub expr: AstExpr,
    }
}

declare_ast_variant! {
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

declare_ast_node! {
    pub struct AstAssignExpr {
        span: Span,
        pub lhs: Box<AstExpr>,
        pub rhs: Box<AstExpr>,
    }
}

declare_ast_node! {
    pub struct AstBinaryOpExpr {
        span: Span,
        pub lhs: Box<AstExpr>,
        pub rhs: Box<AstExpr>,
        pub op: AstBinaryOp,
    }
}

declare_ast_node! {
    pub struct AstUnaryOpExpr {
        span: Span,
        pub operand: Box<AstExpr>,
        pub op: AstUnaryOp,
    }
}

declare_ast_node! {
    pub struct AstIntegerLiteralExpr {
        span: Span,
        pub value: i32,
    }
}

declare_ast_node! {
    pub struct AstBooleanLiteralExpr {
        span: Span,
        pub value: bool,
    }
}

declare_ast_node! {
    pub struct AstDotIndexExpr {
        span: Span,
        pub origin: Box<AstExpr>,
        pub index: AstIdentifier,
    }
}

declare_ast_node! {
    pub struct AstBracketIndexExpr {
        span: Span,
        pub origin: Box<AstExpr>,
        pub index: Box<AstExpr>,
    }
}

declare_ast_node! {
    pub struct AstReferenceExpr {
        span: Span,
        pub name: AstIdentifier,
    }
}

declare_ast_node! {
    pub struct AstCallExpr {
        span: Span,
        pub callee: Box<AstExpr>,
        pub arguments: Vec<AstExpr>,
        pub type_arguments: Vec<AstType>,
    }
}

declare_ast_node! {
    pub struct AstConstructExpr {
        span: Span,
        pub callee: AstType,
        pub arguments: Vec<AstConstructorExprArgument>,
    }
}

declare_ast_node! {
    pub struct AstConstructorExprArgument {
        span: Span,
        pub field: AstIdentifier,
        pub expr: AstExpr,
    }
}

declare_ast_node! {
    pub struct AstGroupExpr {
        span: Span,
        pub inner: Box<AstExpr>,
    }
}

declare_ast_node! {
    /// An identifier.
    ///
    /// This is practically a copy of the `TokenType::Identifier` variant, but we want to be able to
    /// extract them from the AST, as we don't care for storing token types in the AST.
    pub struct AstIdentifier {
        pub name: String,
        span: Span,
    }
}

declare_ast_variant! {
    pub enum AstType {
        Unit(AstUnitType),
        Integer32(AstInteger32Type),
        Pointer(AstPointerType),
        Named(AstNamedType),
        Boolean(AstBooleanType),
    }
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

declare_ast_node! {
    pub struct AstUnitType {
        span: Span,
    }
}

declare_ast_node! {
    pub struct AstInteger32Type {
        span: Span,
    }
}

declare_ast_node! {
    pub struct AstBooleanType {
        span: Span,
    }
}

declare_ast_node! {
    pub struct AstPointerType {
        span: Span,
        pub inner: Box<AstType>,
    }
}

declare_ast_node! {
    pub struct AstNamedType {
        span: Span,
        pub name: AstIdentifier,
    }
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
