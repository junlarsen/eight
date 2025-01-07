//! Textual formatting for HIR modules.
//!
//! This module provides a Wadler-style pretty printer for HIR modules. The format is not intended
//! to be consumed programmatically, but rather to be read by humans as an alternative to the raw
//! Ron format.
//!
//! It is provided on a best-effort basis, and holds no backwards compatibility guarantees. It also
//! invents syntax not found in the base language, such as statement blocks and while loops.

use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use crate::item::{
    HirFunction, HirFunctionParameter, HirInstance, HirIntrinsicFunction, HirRecord, HirTrait,
    HirTraitFunctionItem, HirTypeParameter,
};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirTy, HirVariableTy};
use crate::HirModule;
use eight_diagnostics::ice;
use pretty::RcDoc;

pub struct HirModuleDebugPass();

impl HirModuleDebugPass {
    pub fn format_hir_module_to_string(module: &HirModule) -> String {
        let doc = Self::format_hir_module(module);
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .unwrap_or_else(|_| ice!("failed to render hir module"));
        String::from_utf8(w).unwrap()
    }

    pub fn format_hir_module<'ta>(module: &'ta HirModule<'ta>) -> RcDoc<'ta, ()> {
        RcDoc::text("module")
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append("// module intrinsic scalar types")
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module
                            .intrinsic_scalars
                            .keys()
                            .map(|name| Self::format_hir_intrinsic_scalar(name)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append("// module intrinsic functions")
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module
                            .intrinsic_functions
                            .values()
                            .map(|fun| Self::format_hir_intrinsic_function(fun)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
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
                    .append("// module traits")
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module
                            .traits
                            .values()
                            .map(|r#trait| Self::format_hir_trait_item(r#trait)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("// module instances"))
                    .append(RcDoc::hardline())
                    .append(RcDoc::intersperse(
                        module.instances.values().map(|instance_set| {
                            RcDoc::intersperse(
                                instance_set
                                    .iter()
                                    .map(|instance| Self::format_hir_instance(instance)),
                                RcDoc::hardline(),
                            )
                        }),
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
                            .map(|fun| Self::format_hir_function(fun)),
                        RcDoc::hardline(),
                    ))
                    .append(RcDoc::hardline()),
            )
            .nest(2)
            .group()
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_function<'ta>(function: &'ta HirFunction) -> RcDoc<'ta, ()> {
        RcDoc::text("fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name.name.as_str()))
            .append(Self::format_hir_type_parameters(&function.type_parameters))
            .append(Self::format_function_parameters(&function.parameters))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(function.return_type))
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

    pub fn format_hir_intrinsic_function<'ta>(
        function: &'ta HirIntrinsicFunction,
    ) -> RcDoc<'ta, ()> {
        RcDoc::text("intrinsic_fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name.name.as_str()))
            .append(Self::format_hir_type_parameters(&function.type_parameters))
            .append(Self::format_function_parameters(&function.parameters))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(function.return_type))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_intrinsic_scalar(name: &str) -> RcDoc<()> {
        RcDoc::text("intrinsic_scalar")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_record<'ta>(ty: &'ta HirRecord) -> RcDoc<'ta, ()> {
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
                                        .append(Self::format_hir_ty(ty.ty))
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

    pub fn format_function_parameters<'ta>(
        parameters: &'ta [HirFunctionParameter],
    ) -> RcDoc<'ta, ()> {
        RcDoc::text("(")
            .append(RcDoc::intersperse(
                parameters.iter().map(|p| {
                    RcDoc::text(p.name.name.as_str()).append(
                        RcDoc::text(":")
                            .append(RcDoc::space())
                            .append(Self::format_hir_ty(p.ty)),
                    )
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_type_parameters<'ta>(parameters: &'ta [HirTypeParameter]) -> RcDoc<'ta, ()> {
        if parameters.is_empty() {
            return RcDoc::nil();
        }
        RcDoc::text("<")
            .append(RcDoc::intersperse(
                parameters.iter().map(|p| match p.substitution_name {
                    Some(sub) => Self::format_hir_ty(sub),
                    None => RcDoc::text(p.syntax_name.name.as_str()),
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
    }

    pub fn format_hir_trait_item<'ta>(r#trait: &'ta HirTrait) -> RcDoc<'ta, ()> {
        RcDoc::text("trait")
            .append(RcDoc::space())
            .append(RcDoc::text(r#trait.name.name.as_str()))
            .append(Self::format_hir_type_parameters(
                r#trait.type_parameters.as_slice(),
            ))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        r#trait
                            .members
                            .iter()
                            .map(|f| Self::format_hir_trait_function_item(f)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_trait_function_item<'ta>(
        function: &'ta HirTraitFunctionItem,
    ) -> RcDoc<'ta, ()> {
        RcDoc::text("fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name.name.as_str()))
            .append(Self::format_hir_type_parameters(
                function.type_parameters.as_slice(),
            ))
            .append(RcDoc::space())
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(
                function.parameters.iter().map(|p| {
                    RcDoc::text(p.name.name.as_str()).append(
                        RcDoc::text(":")
                            .append(RcDoc::space())
                            .append(Self::format_hir_ty(p.ty)),
                    )
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(")"))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(function.return_type))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_instance<'ta>(instance: &'ta HirInstance<'ta>) -> RcDoc<'ta, ()> {
        RcDoc::text("instance")
            .append(RcDoc::space())
            .append(&instance.name.name)
            .append(RcDoc::space())
            .append(
                RcDoc::text("{")
                    .append(
                        RcDoc::hardline()
                            .append(RcDoc::intersperse(
                                instance
                                    .members
                                    .iter()
                                    .map(|member| Self::format_hir_function(member)),
                                RcDoc::line(),
                            ))
                            .nest(2)
                            .group(),
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("}")),
            )
    }

    pub fn format_hir_stmt<'ta>(stmt: &'ta HirStmt) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_let_stmt<'ta>(stmt: &'ta HirLetStmt) -> RcDoc<'ta, ()> {
        RcDoc::text("let")
            .append(RcDoc::space())
            .append(RcDoc::text(stmt.name.name.as_str()))
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(stmt.ty))
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&stmt.value))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_return_stmt<'ta>(stmt: &'ta HirReturnStmt) -> RcDoc<'ta, ()> {
        let mut doc = RcDoc::text("return");
        if let Some(value) = &stmt.value {
            doc = doc
                .append(RcDoc::space())
                .append(Self::format_hir_expr(value))
                .append(RcDoc::text(";"));
        }
        doc
    }

    pub fn format_hir_loop_stmt<'ta>(stmt: &'ta HirLoopStmt) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_if_stmt<'ta>(stmt: &'ta HirIfStmt) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_expr_stmt<'ta>(stmt: &'ta HirExprStmt) -> RcDoc<'ta, ()> {
        Self::format_hir_expr(&stmt.expr).append(RcDoc::text(";"))
    }

    pub fn format_hir_block_stmt<'ta>(stmt: &'ta HirBlockStmt) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_expr<'ta>(expr: &'ta HirExpr) -> RcDoc<'ta, ()> {
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
            HirExpr::AddressOf(e) => Self::format_hir_address_of_expr(e),
            HirExpr::Deref(e) => Self::format_hir_deref_expr(e),
        };
        RcDoc::text("(")
            .append(inner)
            .append(RcDoc::space())
            .append(RcDoc::text("as"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(expr.ty()))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_integer_literal_expr<'ta>(expr: &HirIntegerLiteralExpr) -> RcDoc<'ta, ()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_boolean_literal_expr<'ta>(expr: &HirBooleanLiteralExpr) -> RcDoc<'ta, ()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_assign_expr<'ta>(expr: &'ta HirAssignExpr) -> RcDoc<'ta, ()> {
        Self::format_hir_expr(&expr.lhs)
            .append(RcDoc::text(" = "))
            .append(Self::format_hir_expr(&expr.rhs))
    }

    pub fn format_hir_unary_op_expr<'ta>(expr: &'ta HirUnaryOpExpr) -> RcDoc<'ta, ()> {
        RcDoc::text(match &expr.op {
            HirUnaryOp::Not => "!",
            HirUnaryOp::Neg => "-",
        })
        .append(Self::format_hir_expr(&expr.operand))
    }

    pub fn format_hir_binary_op_expr<'ta>(expr: &'ta HirBinaryOpExpr) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_reference_expr<'ta>(expr: &'ta HirReferenceExpr) -> RcDoc<'ta, ()> {
        RcDoc::text(expr.name.name.as_str())
    }

    pub fn format_hir_constant_index_expr<'ta>(expr: &'ta HirConstantIndexExpr) -> RcDoc<'ta, ()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("."))
            .append(expr.index.name.as_str())
    }

    pub fn format_hir_offset_index_expr<'ta>(expr: &'ta HirOffsetIndexExpr) -> RcDoc<'ta, ()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("["))
            .append(Self::format_hir_expr(&expr.index))
            .append(RcDoc::text("]"))
    }

    pub fn format_hir_call_expr<'ta>(expr: &'ta HirCallExpr) -> RcDoc<'ta, ()> {
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

    pub fn format_hir_construct_expr<'ta>(expr: &'ta HirConstructExpr) -> RcDoc<'ta, ()> {
        RcDoc::text("new")
            .append(RcDoc::space())
            .append(Self::format_hir_ty(expr.callee))
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

    pub fn format_hir_construct_expr_argument<'ta>(
        expr: &'ta HirConstructExprArgument,
    ) -> RcDoc<'ta, ()> {
        RcDoc::text(expr.field.name.as_str())
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&expr.expr))
            .append(RcDoc::text(","))
    }

    pub fn format_hir_group_expr<'ta>(expr: &'ta HirGroupExpr) -> RcDoc<'ta, ()> {
        RcDoc::text("(")
            .append(Self::format_hir_expr(&expr.inner))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_address_of_expr<'ta>(expr: &'ta HirAddressOfExpr) -> RcDoc<'ta, ()> {
        RcDoc::text("&").append(Self::format_hir_expr(&expr.inner))
    }

    pub fn format_hir_deref_expr<'ta>(expr: &'ta HirDerefExpr) -> RcDoc<'ta, ()> {
        RcDoc::text("*").append(Self::format_hir_expr(&expr.inner))
    }

    pub fn format_hir_ty<'ta>(ty: &'ta HirTy) -> RcDoc<'ta, ()> {
        match ty {
            HirTy::Integer32(_) => RcDoc::text("i32"),
            HirTy::Boolean(_) => RcDoc::text("bool"),
            HirTy::Unit(_) => RcDoc::text("unit"),
            HirTy::Variable(t) => Self::format_hir_variable_ty(t),
            HirTy::Function(t) => Self::format_hir_function_ty(t),
            HirTy::Nominal(t) => Self::format_hir_nominal_ty(t),
            HirTy::Pointer(t) => Self::format_hir_pointer_ty(t),
            HirTy::Uninitialized(_) => Self::format_hir_uninitialized_ty(ty),
        }
    }

    pub fn format_hir_variable_ty(ty: &HirVariableTy) -> RcDoc<()> {
        RcDoc::text("$").append(RcDoc::text(ty.var.to_string()))
    }

    pub fn format_hir_function_ty<'ta>(ty: &'ta HirFunctionTy) -> RcDoc<'ta, ()> {
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
            .append(Self::format_hir_ty(ty.return_type))
    }

    pub fn format_hir_nominal_ty(ty: &HirNominalTy) -> RcDoc<()> {
        RcDoc::text(ty.name.name.as_str())
    }

    pub fn format_hir_pointer_ty<'ta>(ty: &'ta HirPointerTy) -> RcDoc<'ta, ()> {
        RcDoc::text("*").append(Self::format_hir_ty(ty.inner))
    }

    pub fn format_hir_uninitialized_ty<'ta>(_: &HirTy) -> RcDoc<'ta, ()> {
        RcDoc::text("_")
    }
}
