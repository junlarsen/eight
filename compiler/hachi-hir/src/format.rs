//! Textual formatting for HIR modules.
//!
//! This module provides a Wadler-style pretty printer for HIR modules. The format is not intended
//! to be consumed programmatically, but rather to be read by humans as an alternative to the raw
//! Ron format.
//!
//! It is provided on a best-effort basis, and holds no backwards compatibility guarantees. It also
//! invents syntax not found in the base language, such as statement blocks and while loops.

use crate::expr::{
    HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr, HirCallExpr,
    HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirExpr, HirGroupExpr,
    HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp, HirUnaryOpExpr,
};
use crate::fun::{
    HirFun, HirFunction, HirFunctionParameter, HirFunctionTypeParameter, HirIntrinsicFunction,
};
use crate::rec::HirRecord;
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirReferenceTy, HirTy, HirVariableTy};
use crate::HirModule;
use pretty::RcDoc;

pub struct HirModuleFormatter();

impl HirModuleFormatter {
    pub fn format_hir_module_to_string(module: &HirModule) -> String {
        let doc = Self::format_hir_module(module);
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .expect("ice: failed to render hir module");
        String::from_utf8(w).unwrap()
    }

    pub fn format_hir_module(module: &HirModule) -> RcDoc<()> {
        RcDoc::text("module")
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append("// module types")
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module
                            .records
                            .values()
                            .map(|rec| Self::format_hir_record(rec)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append("// module functions")
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module
                            .functions
                            .values()
                            .map(|fun| Self::format_hir_fun(fun)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline()),
            )
            .nest(2)
            .group()
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_fun(function: &HirFun) -> RcDoc<()> {
        match function {
            HirFun::Function(f) => Self::format_hir_function(f),
            HirFun::Intrinsic(f) => Self::format_hir_intrinsic_function(f),
        }
    }

    pub fn format_hir_function(function: &HirFunction) -> RcDoc<()> {
        RcDoc::text("fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name.name.as_str()))
            .append(Self::format_function_type_parameters(
                &function.type_parameters,
            ))
            .append(Self::format_function_parameters(&function.parameters))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(&function.return_type))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(
                        RcDoc::intersperse(
                            function.body.iter().map(|s| Self::format_hir_stmt(s)),
                            RcDoc::line(),
                        )
                        .append(RcDoc::hardline()),
                    )
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_intrinsic_function(function: &HirIntrinsicFunction) -> RcDoc<()> {
        RcDoc::text("intrinsic_fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name.name.as_str()))
            .append(Self::format_function_type_parameters(
                &function.type_parameters,
            ))
            .append(Self::format_function_parameters(&function.parameters))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(&function.return_type))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_record(ty: &HirRecord) -> RcDoc<()> {
        RcDoc::text("type")
            .append(RcDoc::space())
            .append(RcDoc::text(ty.name.name.as_str()))
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::space())
            .append(
                RcDoc::text("{")
                    .append(
                        RcDoc::hardline()
                            .append(RcDoc::intersperse(
                                ty.fields.iter().map(|(name, ty)| {
                                    RcDoc::text(name.as_str())
                                        .append(RcDoc::text(":"))
                                        .append(RcDoc::space())
                                        .append(Self::format_hir_ty(ty.ty.as_ref()))
                                        .append(RcDoc::text(","))
                                }),
                                RcDoc::line(),
                            ))
                            .nest(2)
                            .group(),
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("}")),
            )
    }

    pub(super) fn format_function_parameters(
        parameters: &[Box<HirFunctionParameter>],
    ) -> RcDoc<()> {
        RcDoc::text("(")
            .append(RcDoc::intersperse(
                parameters.iter().map(|p| {
                    RcDoc::text(p.name.name.as_str()).append(
                        RcDoc::text(":")
                            .append(RcDoc::space())
                            .append(Self::format_hir_ty(&p.ty)),
                    )
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(")"))
    }

    pub(super) fn format_function_type_parameters(
        parameters: &[Box<HirFunctionTypeParameter>],
    ) -> RcDoc<()> {
        RcDoc::text("<")
            .append(RcDoc::intersperse(
                parameters
                    .iter()
                    .map(|p| RcDoc::text("$").append(RcDoc::text(p.name.to_string()))),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
    }

    pub fn format_hir_stmt(stmt: &HirStmt) -> RcDoc<()> {
        match stmt {
            HirStmt::Let(s) => Self::format_hir_let_stmt(s),
            HirStmt::Return(s) => Self::format_hir_return_stmt(s),
            HirStmt::Loop(s) => Self::format_hir_loop_stmt(s),
            HirStmt::Expr(s) => Self::format_hir_expr_stmt(s),
            HirStmt::If(s) => Self::format_hir_if_stmt(s),
            HirStmt::Break(s) => Self::format_hir_break_stmt(s),
            HirStmt::Continue(s) => Self::format_hir_continue_stmt(s),
            HirStmt::Block(s) => Self::format_hir_block_stmt(s),
        }
    }

    pub fn format_hir_let_stmt(stmt: &HirLetStmt) -> RcDoc<()> {
        RcDoc::text("let")
            .append(RcDoc::space())
            .append(RcDoc::text(stmt.name.name.as_str()))
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(&stmt.r#type))
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&stmt.value))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_return_stmt(stmt: &HirReturnStmt) -> RcDoc<()> {
        let mut doc = RcDoc::text("return");
        if let Some(value) = &stmt.value {
            doc = doc
                .append(RcDoc::space())
                .append(Self::format_hir_expr(value))
                .append(RcDoc::text(";"));
        }
        doc
    }

    pub fn format_hir_loop_stmt(stmt: &HirLoopStmt) -> RcDoc<()> {
        RcDoc::text("while")
            .append(RcDoc::space())
            .append(RcDoc::text("("))
            .append(Self::format_hir_expr(&stmt.condition))
            .append(RcDoc::text(")"))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.body
                            .iter()
                            .map(|s| Self::format_hir_stmt(s))
                            .collect::<Vec<_>>(),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_if_stmt(stmt: &HirIfStmt) -> RcDoc<()> {
        RcDoc::text("if")
            .append(RcDoc::space())
            .append(RcDoc::text("("))
            .append(Self::format_hir_expr(&stmt.condition))
            .append(RcDoc::text(")"))
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.happy_path
                            .iter()
                            .map(|s| Self::format_hir_stmt(s))
                            .collect::<Vec<_>>(),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
            .append(RcDoc::space())
            .append(RcDoc::text("else"))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.unhappy_path
                            .iter()
                            .map(|s| Self::format_hir_stmt(s))
                            .collect::<Vec<_>>(),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_break_stmt(_: &HirBreakStmt) -> RcDoc<()> {
        RcDoc::text("break").append(RcDoc::text(";"))
    }

    pub fn format_hir_continue_stmt(_: &HirContinueStmt) -> RcDoc<()> {
        RcDoc::text("continue").append(RcDoc::text(";"))
    }

    pub fn format_hir_expr_stmt(stmt: &HirExprStmt) -> RcDoc<()> {
        Self::format_hir_expr(&stmt.expr).append(RcDoc::text(";"))
    }

    pub fn format_hir_block_stmt(stmt: &HirBlockStmt) -> RcDoc<()> {
        RcDoc::text("{")
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.body
                            .iter()
                            .map(|s| Self::format_hir_stmt(s))
                            .collect::<Vec<_>>(),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_expr(expr: &HirExpr) -> RcDoc<()> {
        let inner = match expr {
            HirExpr::IntegerLiteral(e) => Self::format_hir_integer_literal_expr(e),
            HirExpr::BooleanLiteral(e) => Self::format_hir_boolean_literal_expr(e),
            HirExpr::Assign(e) => Self::format_hir_assign_expr(e),
            HirExpr::UnaryOp(e) => Self::format_hir_unary_op_expr(e),
            HirExpr::BinaryOp(e) => Self::format_hir_binary_op_expr(e),
            HirExpr::Reference(e) => Self::format_hir_reference_expr(e),
            HirExpr::ConstantIndex(e) => Self::format_hir_constant_index_expr(e),
            HirExpr::OffsetIndex(e) => Self::format_hir_offset_index_expr(e),
            HirExpr::Call(e) => Self::format_hir_call_expr(e),
            HirExpr::Construct(e) => Self::format_hir_construct_expr(e),
            HirExpr::Group(e) => Self::format_hir_group_expr(e),
        };
        inner
            .append(RcDoc::text("::"))
            .append(Self::format_hir_ty(expr.ty()))
    }

    pub fn format_hir_integer_literal_expr(expr: &HirIntegerLiteralExpr) -> RcDoc<()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_boolean_literal_expr(expr: &HirBooleanLiteralExpr) -> RcDoc<()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_assign_expr(expr: &HirAssignExpr) -> RcDoc<()> {
        Self::format_hir_expr(&expr.lhs)
            .append(RcDoc::text(" = "))
            .append(Self::format_hir_expr(&expr.rhs))
    }

    pub fn format_hir_unary_op_expr(expr: &HirUnaryOpExpr) -> RcDoc<()> {
        RcDoc::text(match &expr.op {
            HirUnaryOp::Not => "!",
            HirUnaryOp::Neg => "-",
            HirUnaryOp::Deref => "*",
            HirUnaryOp::AddressOf => "&",
        })
        .append(Self::format_hir_expr(&expr.operand))
    }

    pub fn format_hir_binary_op_expr(expr: &HirBinaryOpExpr) -> RcDoc<()> {
        Self::format_hir_expr(&expr.lhs)
            .append(RcDoc::text(" "))
            .append(RcDoc::text(match &expr.op {
                HirBinaryOp::Add => "+",
                HirBinaryOp::Sub => "-",
                HirBinaryOp::Mul => "*",
                HirBinaryOp::Div => "/",
                HirBinaryOp::Rem => "%",
                HirBinaryOp::Eq => "==",
                HirBinaryOp::Neq => "!=",
                HirBinaryOp::Lt => "<",
                HirBinaryOp::Gt => ">",
                HirBinaryOp::Le => "<=",
                HirBinaryOp::Ge => ">=",
                HirBinaryOp::Lte => "<=",
                HirBinaryOp::Gte => ">=",
                HirBinaryOp::And => "&&",
                HirBinaryOp::Or => "||",
            }))
            .append(RcDoc::text(" "))
            .append(Self::format_hir_expr(&expr.rhs))
    }

    pub fn format_hir_reference_expr(expr: &HirReferenceExpr) -> RcDoc<()> {
        RcDoc::text(expr.name.name.as_str())
    }

    pub fn format_hir_constant_index_expr(expr: &HirConstantIndexExpr) -> RcDoc<()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("."))
            .append(expr.index.name.as_str())
    }

    pub fn format_hir_offset_index_expr(expr: &HirOffsetIndexExpr) -> RcDoc<()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("["))
            .append(Self::format_hir_expr(&expr.index))
            .append(RcDoc::text("]"))
    }

    pub fn format_hir_call_expr(expr: &HirCallExpr) -> RcDoc<()> {
        Self::format_hir_expr(&expr.callee)
            .append(RcDoc::text("::"))
            .append(RcDoc::text("<"))
            .append(RcDoc::intersperse(
                expr.type_arguments
                    .iter()
                    .map(|a| Self::format_hir_ty(a))
                    .collect::<Vec<_>>(),
                RcDoc::text(","),
            ))
            .append(RcDoc::text(">"))
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(
                expr.arguments
                    .iter()
                    .map(|a| Self::format_hir_expr(a))
                    .collect::<Vec<_>>(),
                RcDoc::text(","),
            ))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_construct_expr(expr: &HirConstructExpr) -> RcDoc<()> {
        RcDoc::text("new")
            .append(RcDoc::space())
            .append(Self::format_hir_ty(&expr.callee))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        expr.arguments
                            .iter()
                            .map(|a| Self::format_hir_construct_expr_argument(a)),
                        RcDoc::line(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_construct_expr_argument(expr: &HirConstructExprArgument) -> RcDoc<()> {
        RcDoc::text(expr.field.name.as_str())
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&expr.expr))
            .append(RcDoc::text(","))
    }

    pub fn format_hir_group_expr(expr: &HirGroupExpr) -> RcDoc<()> {
        RcDoc::text("(")
            .append(Self::format_hir_expr(&expr.inner))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_ty(ty: &HirTy) -> RcDoc<()> {
        match ty {
            HirTy::Integer32(_) => RcDoc::text("i32"),
            HirTy::Boolean(_) => RcDoc::text("bool"),
            HirTy::Unit(_) => RcDoc::text("unit"),
            HirTy::Variable(t) => Self::format_hir_variable_ty(t),
            HirTy::Function(t) => Self::format_hir_function_ty(t),
            HirTy::Nominal(t) => Self::format_hir_nominal_ty(t),
            HirTy::Pointer(t) => Self::format_hir_pointer_ty(t),
            HirTy::Reference(t) => Self::format_hir_reference_ty(t),
            HirTy::Uninitialized => Self::format_hir_uninitialized_ty(ty),
        }
    }

    pub fn format_hir_variable_ty(ty: &HirVariableTy) -> RcDoc<()> {
        RcDoc::text("$").append(RcDoc::text(ty.name.to_string()))
    }

    pub fn format_hir_function_ty(ty: &HirFunctionTy) -> RcDoc<()> {
        RcDoc::text("fn")
            .append(RcDoc::text("("))
            .append(
                RcDoc::text("(")
                    .append(RcDoc::intersperse(
                        ty.parameters.iter().map(|p| Self::format_hir_ty(p)),
                        RcDoc::text(", "),
                    ))
                    .append(RcDoc::text(")")),
            )
            .append(RcDoc::text(")"))
            .append(RcDoc::text("->"))
            .append(Self::format_hir_ty(&ty.return_type))
    }

    pub fn format_hir_nominal_ty(ty: &HirNominalTy) -> RcDoc<()> {
        RcDoc::text(ty.name.name.as_str())
    }

    pub fn format_hir_pointer_ty(ty: &HirPointerTy) -> RcDoc<()> {
        RcDoc::text("*").append(Self::format_hir_ty(&ty.inner))
    }

    pub fn format_hir_reference_ty(ty: &HirReferenceTy) -> RcDoc<()> {
        RcDoc::text("&").append(Self::format_hir_ty(&ty.inner))
    }

    pub fn format_hir_uninitialized_ty(_: &HirTy) -> RcDoc<()> {
        RcDoc::text("_")
    }
}
