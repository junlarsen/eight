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
use crate::item::{HirFunction, HirInstance};
use crate::signature::{
    HirFunctionApiSignature, HirFunctionParameterApiSignature, HirInstanceApiSignature,
    HirStructApiSignature, HirTraitApiSignature, HirTypeApiSignature, HirTypeParameterApiSignature,
};
use crate::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirTy, HirVariableTy};
use crate::{HirModule, LinkageType};
use eight_diagnostics::ice;
use pretty::RcDoc;

pub struct HirModuleDebugPass();

impl HirModuleDebugPass {
    pub fn format_hir_module_to_string<'hir>(module: &'hir HirModule<'hir>) -> String {
        let doc = Self::format_hir_module(module);
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .unwrap_or_else(|_| ice!("failed to render hir module"));
        String::from_utf8(w).unwrap()
    }

    pub fn format_hir_module<'hir>(module: &'hir HirModule<'hir>) -> RcDoc<'hir, ()> {
        RcDoc::text("hir_module")
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::text("declares"))
                    .append(RcDoc::space())
                    .append(RcDoc::text("{"))
                    .append(
                        RcDoc::hardline()
                            .append(RcDoc::text("// module types"))
                            .append(RcDoc::hardline())
                            .append(
                                RcDoc::intersperse(
                                    module.signature.types.iter().map(|(name, sig)| {
                                        Self::format_hir_type_signature(name, sig)
                                    }),
                                    RcDoc::hardline(),
                                )
                                .append(RcDoc::hardline())
                                .append(RcDoc::hardline())
                                .append(RcDoc::text("// module struct types"))
                                .append(RcDoc::hardline())
                                .append(
                                    RcDoc::intersperse(
                                        module.signature.structs.iter().map(|(name, sig)| {
                                            Self::format_hir_struct_signature(name, sig)
                                        }),
                                        RcDoc::hardline(),
                                    )
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::text("// module functions"))
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::intersperse(
                                        module.signature.functions.iter().map(|(name, sig)| {
                                            Self::format_hir_function_signature(name, sig)
                                        }),
                                        RcDoc::hardline(),
                                    ))
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::hardline())
                                    .append("// module traits")
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::intersperse(
                                        module.signature.traits.iter().map(|(name, sig)| {
                                            Self::format_hir_trait_signature(name, sig)
                                        }),
                                        RcDoc::hardline(),
                                    ))
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::hardline())
                                    .append(RcDoc::text("// module instances"))
                                    .append(RcDoc::hardline())
                                    .append(
                                        RcDoc::intersperse(
                                            module.signature.instances.iter().map(|sig| {
                                                Self::format_hir_instance_signature(
                                                    sig.trait_name,
                                                    sig,
                                                )
                                            }),
                                            RcDoc::hardline(),
                                        ),
                                    ),
                                ),
                            )
                            .nest(2)
                            .group(),
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("}"))
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("defining"))
                    .append(RcDoc::space())
                    .append(RcDoc::text("{"))
                    .append(
                        RcDoc::hardline()
                            .append("// module functions")
                            .append(RcDoc::hardline())
                            .append(RcDoc::intersperse(
                                module
                                    .body
                                    .functions
                                    .values()
                                    .filter(|f| f.linkage_type == LinkageType::Eight)
                                    .map(|f| Self::format_hir_function(f)),
                                RcDoc::hardline(),
                            ))
                            .append(RcDoc::hardline())
                            .append("// module intrinsic functions")
                            .append(RcDoc::hardline())
                            .append(RcDoc::intersperse(
                                module
                                    .body
                                    .instances
                                    .iter()
                                    .map(|i| Self::format_hir_instance(i)),
                                RcDoc::hardline(),
                            ))
                            .append(RcDoc::hardline())
                            .nest(2)
                            .group(),
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::text("}")),
            )
            .nest(2)
            .group()
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_function<'hir>(function: &'hir HirFunction) -> RcDoc<'hir, ()> {
        RcDoc::text("fn")
            .append(RcDoc::space())
            .append(RcDoc::text(function.name))
            .append(RcDoc::text("<"))
            .append(RcDoc::intersperse(
                function.signature.type_parameters.iter().map(|p| {
                    match function.type_parameter_substitutions.get(p.name) {
                        Some(t) => Self::format_hir_ty(t),
                        None => RcDoc::text(p.name),
                    }
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(
                function.signature.parameters.iter().map(|p| {
                    RcDoc::text(p.name)
                        .append(RcDoc::text(":"))
                        .append(RcDoc::space())
                        .append(Self::format_hir_ty(p.ty))
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(")"))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(
                match &function.instantiated_return_type {
                    Some(t) => t,
                    None => function.signature.return_type,
                },
            ))
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

    pub fn format_hir_instance<'hir>(instance: &'hir HirInstance<'hir>) -> RcDoc<'hir, ()> {
        RcDoc::text("instance")
            .append(RcDoc::space())
            .append(RcDoc::text(instance.name))
            .append(RcDoc::text("<"))
            .append(RcDoc::intersperse(
                instance
                    .signature
                    .type_arguments
                    .iter()
                    .map(|p| Self::format_hir_ty(p)),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        instance
                            .members
                            .iter()
                            .map(|f| Self::format_hir_function(f)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_function_signature<'hir>(
        name: &'hir str,
        signature: &'hir HirFunctionApiSignature<'hir>,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("fn")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(Self::format_hir_type_parameter_signature(
                signature.type_parameters.as_slice(),
            ))
            .append(Self::format_function_parameters(
                signature.parameters.as_slice(),
            ))
            .append(RcDoc::space())
            .append(RcDoc::text("->"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(signature.return_type))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_type_signature<'hir>(
        name: &'hir str,
        _: &'hir HirTypeApiSignature,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("type")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_struct_signature<'hir>(
        name: &'hir str,
        ty: &'hir HirStructApiSignature,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("type")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::space())
            .append(
                RcDoc::text("{")
                    .append(
                        RcDoc::hardline()
                            .append(RcDoc::intersperse(
                                ty.fields.iter().map(|(name, ty)| {
                                    RcDoc::text(*name)
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

    pub fn format_function_parameters<'hir>(
        parameters: &'hir [&'hir HirFunctionParameterApiSignature],
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("(")
            .append(RcDoc::intersperse(
                parameters.iter().map(|p| {
                    RcDoc::text(p.name).append(
                        RcDoc::text(":")
                            .append(RcDoc::space())
                            .append(Self::format_hir_ty(p.ty)),
                    )
                }),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_instance_signature<'hir>(
        name: &'hir str,
        sig: &'hir HirInstanceApiSignature,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("instance")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(RcDoc::text("<"))
            .append(RcDoc::intersperse(
                sig.type_arguments.iter().map(|p| Self::format_hir_ty(p)),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        sig.methods
                            .iter()
                            .map(|(name, sig)| Self::format_hir_function_signature(name, sig)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_trait_signature<'hir>(
        name: &'hir str,
        sig: &'hir HirTraitApiSignature,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text("trait")
            .append(RcDoc::space())
            .append(RcDoc::text(name))
            .append(Self::format_hir_type_parameter_signature(
                sig.type_parameters.as_slice(),
            ))
            .append(RcDoc::space())
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        sig.methods
                            .iter()
                            .map(|(name, sig)| Self::format_hir_function_signature(name, sig)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_type_parameter_signature<'hir>(
        parameters: &[&'hir HirTypeParameterApiSignature],
    ) -> RcDoc<'hir, ()> {
        if parameters.is_empty() {
            return RcDoc::nil();
        }
        RcDoc::text("<")
            .append(RcDoc::intersperse(
                parameters.iter().map(|p| RcDoc::text(p.name)),
                RcDoc::text(", "),
            ))
            .append(RcDoc::text(">"))
    }

    pub fn format_hir_stmt<'hir>(stmt: &'hir HirStmt) -> RcDoc<'hir, ()> {
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

    pub fn format_hir_let_stmt<'hir>(stmt: &'hir HirLetStmt) -> RcDoc<'hir, ()> {
        RcDoc::text("let")
            .append(RcDoc::space())
            .append(RcDoc::text(stmt.name))
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_ty(stmt.ty))
            .append(RcDoc::space())
            .append(RcDoc::text("="))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&stmt.value))
            .append(RcDoc::text(";"))
    }

    pub fn format_hir_return_stmt<'hir>(stmt: &'hir HirReturnStmt) -> RcDoc<'hir, ()> {
        let mut doc = RcDoc::text("return");
        if let Some(value) = &stmt.value {
            doc = doc
                .append(RcDoc::space())
                .append(Self::format_hir_expr(value))
                .append(RcDoc::text(";"));
        }
        doc
    }

    pub fn format_hir_loop_stmt<'hir>(stmt: &'hir HirLoopStmt) -> RcDoc<'hir, ()> {
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
                        stmt.body.iter().map(|s| Self::format_hir_stmt(s)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_if_stmt<'hir>(stmt: &'hir HirIfStmt) -> RcDoc<'hir, ()> {
        RcDoc::text("if")
            .append(RcDoc::space())
            .append(RcDoc::text("("))
            .append(Self::format_hir_expr(&stmt.condition))
            .append(RcDoc::text(")"))
            .append(RcDoc::text("{"))
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.happy_path.iter().map(|s| Self::format_hir_stmt(s)),
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
                        stmt.unhappy_path.iter().map(|s| Self::format_hir_stmt(s)),
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

    pub fn format_hir_expr_stmt<'hir>(stmt: &'hir HirExprStmt) -> RcDoc<'hir, ()> {
        Self::format_hir_expr(&stmt.expr).append(RcDoc::text(";"))
    }

    pub fn format_hir_block_stmt<'hir>(stmt: &'hir HirBlockStmt) -> RcDoc<'hir, ()> {
        RcDoc::text("{")
            .append(
                RcDoc::hardline()
                    .append(RcDoc::intersperse(
                        stmt.body.iter().map(|s| Self::format_hir_stmt(s)),
                        RcDoc::hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(RcDoc::hardline())
            .append(RcDoc::text("}"))
    }

    pub fn format_hir_expr<'hir>(expr: &'hir HirExpr) -> RcDoc<'hir, ()> {
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

    pub fn format_hir_integer_literal_expr<'hir>(expr: &HirIntegerLiteralExpr) -> RcDoc<'hir, ()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_boolean_literal_expr<'hir>(expr: &HirBooleanLiteralExpr) -> RcDoc<'hir, ()> {
        RcDoc::text(expr.value.to_string())
    }

    pub fn format_hir_assign_expr<'hir>(expr: &'hir HirAssignExpr) -> RcDoc<'hir, ()> {
        Self::format_hir_expr(&expr.lhs)
            .append(RcDoc::text(" = "))
            .append(Self::format_hir_expr(&expr.rhs))
    }

    pub fn format_hir_unary_op_expr<'hir>(expr: &'hir HirUnaryOpExpr) -> RcDoc<'hir, ()> {
        RcDoc::text(match &expr.op {
            HirUnaryOp::Not => "!",
            HirUnaryOp::Neg => "-",
        })
        .append(Self::format_hir_expr(&expr.operand))
    }

    pub fn format_hir_binary_op_expr<'hir>(expr: &'hir HirBinaryOpExpr) -> RcDoc<'hir, ()> {
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

    pub fn format_hir_reference_expr<'hir>(expr: &'hir HirReferenceExpr) -> RcDoc<'hir, ()> {
        RcDoc::text(expr.name)
    }

    pub fn format_hir_constant_index_expr<'hir>(
        expr: &'hir HirConstantIndexExpr,
    ) -> RcDoc<'hir, ()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("."))
            .append(expr.index)
    }

    pub fn format_hir_offset_index_expr<'hir>(expr: &'hir HirOffsetIndexExpr) -> RcDoc<'hir, ()> {
        Self::format_hir_expr(&expr.origin)
            .append(RcDoc::text("["))
            .append(Self::format_hir_expr(&expr.index))
            .append(RcDoc::text("]"))
    }

    pub fn format_hir_call_expr<'hir>(expr: &'hir HirCallExpr) -> RcDoc<'hir, ()> {
        Self::format_hir_expr(&expr.callee)
            .append(RcDoc::text("::"))
            .append(RcDoc::text("<"))
            .append(RcDoc::intersperse(
                expr.type_arguments.iter().map(|a| Self::format_hir_ty(a)),
                RcDoc::text(","),
            ))
            .append(RcDoc::text(">"))
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(
                expr.arguments.iter().map(|a| Self::format_hir_expr(a)),
                RcDoc::text(","),
            ))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_construct_expr<'hir>(expr: &'hir HirConstructExpr) -> RcDoc<'hir, ()> {
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

    pub fn format_hir_construct_expr_argument<'hir>(
        expr: &'hir HirConstructExprArgument,
    ) -> RcDoc<'hir, ()> {
        RcDoc::text(expr.field)
            .append(RcDoc::text(":"))
            .append(RcDoc::space())
            .append(Self::format_hir_expr(&expr.expr))
            .append(RcDoc::text(","))
    }

    pub fn format_hir_group_expr<'hir>(expr: &'hir HirGroupExpr) -> RcDoc<'hir, ()> {
        RcDoc::text("(")
            .append(Self::format_hir_expr(&expr.inner))
            .append(RcDoc::text(")"))
    }

    pub fn format_hir_address_of_expr<'hir>(expr: &'hir HirAddressOfExpr) -> RcDoc<'hir, ()> {
        RcDoc::text("&").append(Self::format_hir_expr(&expr.inner))
    }

    pub fn format_hir_deref_expr<'hir>(expr: &'hir HirDerefExpr) -> RcDoc<'hir, ()> {
        RcDoc::text("*").append(Self::format_hir_expr(&expr.inner))
    }

    pub fn format_hir_ty<'hir>(ty: &'hir HirTy) -> RcDoc<'hir, ()> {
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
        RcDoc::text("$")
            .append(RcDoc::text(ty.depth.to_string()))
            .append(RcDoc::text("@"))
            .append(RcDoc::text(ty.index.to_string()))
    }

    pub fn format_hir_function_ty<'hir>(ty: &'hir HirFunctionTy) -> RcDoc<'hir, ()> {
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

    pub fn format_hir_nominal_ty<'hir>(ty: &'hir HirNominalTy) -> RcDoc<'hir, ()> {
        RcDoc::text(ty.name)
    }

    pub fn format_hir_pointer_ty<'hir>(ty: &'hir HirPointerTy) -> RcDoc<'hir, ()> {
        RcDoc::text("*").append(Self::format_hir_ty(ty.inner))
    }

    pub fn format_hir_uninitialized_ty<'hir>(_: &HirTy) -> RcDoc<'hir, ()> {
        RcDoc::text("_")
    }
}
