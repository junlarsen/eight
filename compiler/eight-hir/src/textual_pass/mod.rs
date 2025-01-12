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
use pretty::{Arena, DocAllocator, DocBuilder};

#[derive(Default)]
pub struct HirModuleTextualPass<'a> {
    arena: Arena<'a>,
}

pub type Document<'a> = DocBuilder<'a, Arena<'a>>;

impl<'a> HirModuleTextualPass<'a> {
    pub fn format_doc_to_string(doc: DocBuilder<'a, Arena<'a>>) -> String {
        let mut w = Vec::new();
        doc.render(80, &mut w)
            .unwrap_or_else(|_| ice!("failed to render hir module"));
        String::from_utf8(w).unwrap()
    }

    pub fn visit_module<'hir: 'a>(
        &'a self,
        module: &'hir HirModule<'hir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("hir_module")
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.text("declares"))
                    .append(self.arena.space())
                    .append(self.arena.text("{"))
                    .append(
                        self.arena
                            .hardline()
                            .append(self.arena.text("// module types"))
                            .append(self.arena.hardline())
                            .append(
                                self.arena
                                    .intersperse(
                                        module.signature.types.iter().map(|(name, sig)| {
                                            self.visit_type_signature(name, sig)
                                        }),
                                        self.arena.hardline(),
                                    )
                                    .append(self.arena.hardline())
                                    .append(self.arena.hardline())
                                    .append(self.arena.text("// module struct types"))
                                    .append(self.arena.hardline())
                                    .append(
                                        self.arena
                                            .intersperse(
                                                module.signature.structs.iter().map(
                                                    |(name, sig)| {
                                                        self.visit_struct_signature(name, sig)
                                                    },
                                                ),
                                                self.arena.hardline(),
                                            )
                                            .append(self.arena.hardline())
                                            .append(self.arena.hardline())
                                            .append(self.arena.text("// module functions"))
                                            .append(self.arena.hardline())
                                            .append(self.arena.intersperse(
                                                module.signature.functions.iter().map(
                                                    |(name, sig)| {
                                                        self.visit_function_signature(name, sig)
                                                    },
                                                ),
                                                self.arena.hardline(),
                                            ))
                                            .append(self.arena.hardline())
                                            .append(self.arena.hardline())
                                            .append("// module traits")
                                            .append(self.arena.hardline())
                                            .append(self.arena.intersperse(
                                                module.signature.traits.iter().map(
                                                    |(name, sig)| {
                                                        self.visit_trait_signature(name, sig)
                                                    },
                                                ),
                                                self.arena.hardline(),
                                            ))
                                            .append(self.arena.hardline())
                                            .append(self.arena.hardline())
                                            .append(self.arena.text("// module instances"))
                                            .append(self.arena.hardline())
                                            .append(self.arena.intersperse(
                                                module.signature.instances.iter().map(|sig| {
                                                    self.visit_instance_signature(
                                                        sig.trait_name,
                                                        sig,
                                                    )
                                                }),
                                                self.arena.hardline(),
                                            )),
                                    ),
                            )
                            .nest(2)
                            .group(),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.text("}"))
                    .append(self.arena.hardline())
                    .append(self.arena.hardline())
                    .append(self.arena.text("defining"))
                    .append(self.arena.space())
                    .append(self.arena.text("{"))
                    .append(
                        self.arena
                            .hardline()
                            .append("// module functions")
                            .append(self.arena.hardline())
                            .append(
                                self.arena.intersperse(
                                    module
                                        .body
                                        .functions
                                        .values()
                                        .filter(|f| f.linkage_type == LinkageType::Eight)
                                        .map(|f| self.visit_function(f)),
                                    self.arena.hardline(),
                                ),
                            )
                            .append(self.arena.hardline())
                            .append("// module intrinsic functions")
                            .append(self.arena.hardline())
                            .append(self.arena.intersperse(
                                module.body.instances.iter().map(|i| self.visit_instance(i)),
                                self.arena.hardline(),
                            ))
                            .append(self.arena.hardline())
                            .nest(2)
                            .group(),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.text("}")),
            )
            .nest(2)
            .group()
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_function<'hir: 'a>(
        &'a self,
        function: &'hir HirFunction,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("fn")
            .append(self.arena.space())
            .append(self.arena.text(function.name))
            .append(self.arena.text("<"))
            .append(self.arena.intersperse(
                function.signature.type_parameters.iter().map(|p| {
                    match function.type_parameter_substitutions.get(p.name) {
                        Some(t) => self.visit_ty(t),
                        None => self.arena.text(p.name),
                    }
                }),
                self.arena.text(", "),
            ))
            .append(self.arena.text(">"))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                function.signature.parameters.iter().map(|p| {
                    self.arena
                        .text(p.name)
                        .append(self.arena.text(":"))
                        .append(self.arena.space())
                        .append(self.visit_ty(p.ty))
                }),
                self.arena.text(", "),
            ))
            .append(self.arena.text(")"))
            .append(self.arena.space())
            .append(self.arena.text("->"))
            .append(self.arena.space())
            .append(self.visit_ty(match &function.instantiated_return_type {
                Some(t) => t,
                None => function.signature.return_type,
            }))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena
                            .intersperse(
                                function.body.iter().map(|s| self.visit_stmt(s)),
                                self.arena.line(),
                            )
                            .append(self.arena.hardline()),
                    )
                    .nest(2)
                    .group(),
            )
            .append(self.arena.text("}"))
    }

    pub fn visit_instance<'hir: 'a>(
        &'a self,
        instance: &'hir HirInstance<'hir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("instance")
            .append(self.arena.space())
            .append(self.arena.text(instance.name))
            .append(self.arena.text("<"))
            .append(
                self.arena.intersperse(
                    instance
                        .signature
                        .type_arguments
                        .iter()
                        .map(|p| self.visit_ty(p)),
                    self.arena.text(", "),
                ),
            )
            .append(self.arena.text(">"))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        instance.members.iter().map(|f| self.visit_function(f)),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_function_signature<'hir: 'a>(
        &'a self,
        name: &'hir str,
        signature: &'hir HirFunctionApiSignature<'hir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("fn")
            .append(self.arena.space())
            .append(self.arena.text(name))
            .append(self.visit_type_parameter_signature(signature.type_parameters.as_slice()))
            .append(self.visit_function_parameter_list(signature.parameters.as_slice()))
            .append(self.arena.space())
            .append(self.arena.text("->"))
            .append(self.arena.space())
            .append(self.visit_ty(signature.return_type))
            .append(self.arena.text(";"))
    }

    pub fn visit_type_signature<'hir: 'a>(
        &'a self,
        name: &'hir str,
        _: &'hir HirTypeApiSignature<'hir>,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("type")
            .append(self.arena.space())
            .append(self.arena.text(name))
            .append(self.arena.text(";"))
    }

    pub fn visit_struct_signature<'hir: 'a>(
        &'a self,
        name: &'hir str,
        ty: &'hir HirStructApiSignature,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("struct")
            .append(self.arena.space())
            .append(self.arena.text(name))
            .append(self.arena.space())
            .append(
                self.arena
                    .text("{")
                    .append(
                        self.arena
                            .hardline()
                            .append(self.arena.intersperse(
                                ty.fields.iter().map(|(name, ty)| {
                                    self.arena
                                        .text(*name)
                                        .append(self.arena.text(":"))
                                        .append(self.arena.space())
                                        .append(self.visit_ty(ty.ty))
                                        .append(self.arena.text(","))
                                }),
                                self.arena.line(),
                            ))
                            .nest(2)
                            .group(),
                    )
                    .append(self.arena.hardline())
                    .append(self.arena.text("}")),
            )
    }

    pub fn visit_function_parameter_list<'hir: 'a>(
        &'a self,
        parameters: &'hir [&'hir HirFunctionParameterApiSignature],
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("(")
            .append(self.arena.intersperse(
                parameters.iter().map(|p| {
                    self.arena.text(p.name).append(
                        self.arena
                            .text(":")
                            .append(self.arena.space())
                            .append(self.visit_ty(p.ty)),
                    )
                }),
                self.arena.text(", "),
            ))
            .append(self.arena.text(")"))
    }

    pub fn visit_instance_signature<'hir: 'a>(
        &'a self,
        name: &'hir str,
        sig: &'hir HirInstanceApiSignature,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("instance")
            .append(self.arena.space())
            .append(self.arena.text(name))
            .append(self.arena.text("<"))
            .append(self.arena.intersperse(
                sig.type_arguments.iter().map(|p| self.visit_ty(p)),
                self.arena.text(", "),
            ))
            .append(self.arena.text(">"))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            sig.methods
                                .iter()
                                .map(|(name, sig)| self.visit_function_signature(name, sig)),
                            self.arena.hardline(),
                        ),
                    )
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_trait_signature<'hir: 'a>(
        &'a self,
        name: &'hir str,
        sig: &'hir HirTraitApiSignature,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("trait")
            .append(self.arena.space())
            .append(self.arena.text(name))
            .append(self.visit_type_parameter_signature(sig.type_parameters.as_slice()))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            sig.methods
                                .iter()
                                .map(|(name, sig)| self.visit_function_signature(name, sig)),
                            self.arena.hardline(),
                        ),
                    )
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_type_parameter_signature<'hir: 'a>(
        &'a self,
        parameters: &[&'hir HirTypeParameterApiSignature],
    ) -> DocBuilder<Arena<'a>> {
        if parameters.is_empty() {
            return self.arena.nil();
        }
        self.arena
            .text("<")
            .append(self.arena.intersperse(
                parameters.iter().map(|p| self.arena.text(p.name)),
                self.arena.text(", "),
            ))
            .append(self.arena.text(">"))
    }

    pub fn visit_stmt<'hir: 'a>(&'a self, stmt: &'hir HirStmt) -> DocBuilder<Arena<'a>> {
        match stmt {
            HirStmt::Let(s) => self.visit_let_stmt(s),
            HirStmt::Return(s) => self.visit_return_stmt(s),
            HirStmt::Loop(s) => self.visit_loop_stmt(s),
            HirStmt::Expr(s) => self.visit_expr_stmt(s),
            HirStmt::If(s) => self.visit_if_stmt(s),
            HirStmt::Break(s) => self.visit_break_stmt(s),
            HirStmt::Continue(s) => self.visit_continue_stmt(s),
            HirStmt::Block(s) => self.visit_block_stmt(s),
        }
    }

    pub fn visit_let_stmt<'hir: 'a>(&'a self, stmt: &'hir HirLetStmt) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("let")
            .append(self.arena.space())
            .append(self.arena.text(stmt.name))
            .append(self.arena.text(":"))
            .append(self.arena.space())
            .append(self.visit_ty(stmt.ty))
            .append(self.arena.space())
            .append(self.arena.text("="))
            .append(self.arena.space())
            .append(self.visit_expr(&stmt.value))
            .append(self.arena.text(";"))
    }

    pub fn visit_return_stmt<'hir: 'a>(
        &'a self,
        stmt: &'hir HirReturnStmt,
    ) -> DocBuilder<Arena<'a>> {
        let mut doc = self.arena.text("return");
        if let Some(value) = &stmt.value {
            doc = doc
                .append(self.arena.space())
                .append(self.visit_expr(value))
                .append(self.arena.text(";"));
        }
        doc
    }

    pub fn visit_loop_stmt<'hir: 'a>(&'a self, stmt: &'hir HirLoopStmt) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("while")
            .append(self.arena.space())
            .append(self.arena.text("("))
            .append(self.visit_expr(&stmt.condition))
            .append(self.arena.text(")"))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        stmt.body.iter().map(|s| self.visit_stmt(s)),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_if_stmt<'hir: 'a>(&'a self, stmt: &'hir HirIfStmt) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("if")
            .append(self.arena.space())
            .append(self.arena.text("("))
            .append(self.visit_expr(&stmt.condition))
            .append(self.arena.text(")"))
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        stmt.happy_path.iter().map(|s| self.visit_stmt(s)),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
            .append(self.arena.space())
            .append(self.arena.text("else"))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        stmt.unhappy_path.iter().map(|s| self.visit_stmt(s)),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_break_stmt(&'a self, _: &HirBreakStmt) -> DocBuilder<Arena<'a>> {
        self.arena.text("break").append(self.arena.text(";"))
    }

    pub fn visit_continue_stmt(&'a self, _: &HirContinueStmt) -> DocBuilder<Arena<'a>> {
        self.arena.text("continue").append(self.arena.text(";"))
    }

    pub fn visit_expr_stmt<'hir: 'a>(&'a self, stmt: &'hir HirExprStmt) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&stmt.expr).append(self.arena.text(";"))
    }

    pub fn visit_block_stmt<'hir: 'a>(&'a self, stmt: &'hir HirBlockStmt) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("{")
            .append(
                self.arena
                    .hardline()
                    .append(self.arena.intersperse(
                        stmt.body.iter().map(|s| self.visit_stmt(s)),
                        self.arena.hardline(),
                    ))
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_expr<'hir: 'a>(&'a self, expr: &'hir HirExpr) -> DocBuilder<Arena<'a>> {
        let inner = match expr {
            HirExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            HirExpr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            HirExpr::Assign(e) => self.visit_assign_expr(e),
            HirExpr::UnaryOp(e) => self.visit_unary_op_expr(e),
            HirExpr::BinaryOp(e) => self.visit_binary_op_expr(e),
            HirExpr::Reference(e) => self.visit_reference_expr(e),
            HirExpr::ConstantIndex(e) => self.visit_constant_index_expr(e),
            HirExpr::OffsetIndex(e) => self.visit_offset_index_expr(e),
            HirExpr::Call(e) => self.visit_call_expr(e),
            HirExpr::Construct(e) => self.visit_construct_expr(e),
            HirExpr::Group(e) => self.visit_group_expr(e),
            HirExpr::AddressOf(e) => self.visit_address_of_expr(e),
            HirExpr::Deref(e) => self.visit_deref_expr(e),
        };
        self.arena
            .text("(")
            .append(inner)
            .append(self.arena.space())
            .append(self.arena.text("as"))
            .append(self.arena.space())
            .append(self.visit_ty(expr.ty()))
            .append(self.arena.text(")"))
    }

    pub fn visit_integer_literal_expr<'hir: 'a>(
        &'a self,
        expr: &HirIntegerLiteralExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena.text(expr.value.to_string())
    }

    pub fn visit_boolean_literal_expr<'hir: 'a>(
        &'a self,
        expr: &HirBooleanLiteralExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena.text(expr.value.to_string())
    }

    pub fn visit_assign_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirAssignExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&expr.lhs)
            .append(self.arena.text(" = "))
            .append(self.visit_expr(&expr.rhs))
    }

    pub fn visit_unary_op_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirUnaryOpExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text(match &expr.op {
                HirUnaryOp::Not => "!",
                HirUnaryOp::Neg => "-",
            })
            .append(self.visit_expr(&expr.operand))
    }

    pub fn visit_binary_op_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirBinaryOpExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&expr.lhs)
            .append(self.arena.text(" "))
            .append(self.arena.text(match &expr.op {
                HirBinaryOp::Add => "+",
                HirBinaryOp::Sub => "-",
                HirBinaryOp::Mul => "*",
                HirBinaryOp::Div => "/",
                HirBinaryOp::Rem => "%",
                HirBinaryOp::Eq => "==",
                HirBinaryOp::Neq => "!=",
                HirBinaryOp::Lt => "<",
                HirBinaryOp::Gt => ">",
                HirBinaryOp::Lte => "<=",
                HirBinaryOp::Gte => ">=",
                HirBinaryOp::And => "&&",
                HirBinaryOp::Or => "||",
            }))
            .append(self.arena.text(" "))
            .append(self.visit_expr(&expr.rhs))
    }

    pub fn visit_reference_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirReferenceExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena.text(expr.name)
    }

    pub fn visit_constant_index_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirConstantIndexExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&expr.origin)
            .append(self.arena.text("."))
            .append(expr.index)
    }

    pub fn visit_offset_index_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirOffsetIndexExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&expr.origin)
            .append(self.arena.text("["))
            .append(self.visit_expr(&expr.index))
            .append(self.arena.text("]"))
    }

    pub fn visit_call_expr<'hir: 'a>(&'a self, expr: &'hir HirCallExpr) -> DocBuilder<Arena<'a>> {
        self.visit_expr(&expr.callee)
            .append(self.arena.text("::"))
            .append(self.arena.text("<"))
            .append(self.arena.intersperse(
                expr.type_arguments.iter().map(|a| self.visit_ty(a)),
                self.arena.text(","),
            ))
            .append(self.arena.text(">"))
            .append(self.arena.text("("))
            .append(self.arena.intersperse(
                expr.arguments.iter().map(|a| self.visit_expr(a)),
                self.arena.text(","),
            ))
            .append(self.arena.text(")"))
    }

    pub fn visit_construct_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirConstructExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("new")
            .append(self.arena.space())
            .append(self.visit_ty(expr.callee))
            .append(self.arena.space())
            .append(self.arena.text("{"))
            .append(
                self.arena
                    .hardline()
                    .append(
                        self.arena.intersperse(
                            expr.arguments
                                .iter()
                                .map(|a| self.visit_construct_expr_argument(a)),
                            self.arena.line(),
                        ),
                    )
                    .nest(2)
                    .group(),
            )
            .append(self.arena.hardline())
            .append(self.arena.text("}"))
    }

    pub fn visit_construct_expr_argument<'hir: 'a>(
        &'a self,
        expr: &'hir HirConstructExprArgument,
    ) -> DocBuilder<Arena<'a>> {
        self.arena
            .text(expr.field)
            .append(self.arena.text(":"))
            .append(self.arena.space())
            .append(self.visit_expr(&expr.expr))
            .append(self.arena.text(","))
    }

    pub fn visit_group_expr<'hir: 'a>(&'a self, expr: &'hir HirGroupExpr) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("(")
            .append(self.visit_expr(&expr.inner))
            .append(self.arena.text(")"))
    }

    pub fn visit_address_of_expr<'hir: 'a>(
        &'a self,
        expr: &'hir HirAddressOfExpr,
    ) -> DocBuilder<Arena<'a>> {
        self.arena.text("&").append(self.visit_expr(&expr.inner))
    }

    pub fn visit_deref_expr<'hir: 'a>(&'a self, expr: &'hir HirDerefExpr) -> DocBuilder<Arena<'a>> {
        self.arena.text("*").append(self.visit_expr(&expr.inner))
    }

    pub fn visit_ty<'hir: 'a>(&'a self, ty: &'hir HirTy) -> DocBuilder<Arena<'a>> {
        match ty {
            HirTy::Integer32(_) => self.arena.text("i32"),
            HirTy::Boolean(_) => self.arena.text("bool"),
            HirTy::Unit(_) => self.arena.text("unit"),
            HirTy::Variable(t) => self.visit_variable_ty(t),
            HirTy::Function(t) => self.visit_function_ty(t),
            HirTy::Nominal(t) => self.visit_nominal_ty(t),
            HirTy::Pointer(t) => self.visit_pointer_ty(t),
            HirTy::Uninitialized(_) => self.visit_uninitialized_ty(ty),
        }
    }

    pub fn visit_variable_ty<'hir: 'a>(&'a self, ty: &'hir HirVariableTy) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("$")
            .append(self.arena.text(ty.depth.to_string()))
            .append(self.arena.text("@"))
            .append(self.arena.text(ty.index.to_string()))
    }

    pub fn visit_function_ty<'hir: 'a>(&'a self, ty: &'hir HirFunctionTy) -> DocBuilder<Arena<'a>> {
        self.arena
            .text("fn")
            .append(self.arena.text("("))
            .append(
                self.arena
                    .text("(")
                    .append(self.arena.intersperse(
                        ty.parameters.iter().map(|p| self.visit_ty(p)),
                        self.arena.text(", "),
                    ))
                    .append(self.arena.text(")")),
            )
            .append(self.arena.text(")"))
            .append(self.arena.text("->"))
            .append(self.visit_ty(ty.return_type))
    }

    pub fn visit_nominal_ty<'hir: 'a>(&'a self, ty: &'hir HirNominalTy) -> DocBuilder<Arena<'a>> {
        self.arena.text(ty.name)
    }

    pub fn visit_pointer_ty<'hir: 'a>(&'a self, ty: &'hir HirPointerTy) -> DocBuilder<Arena<'a>> {
        self.arena.text("*").append(self.visit_ty(ty.inner))
    }

    pub fn visit_uninitialized_ty<'hir: 'a>(&'a self, _: &HirTy) -> DocBuilder<Arena<'a>> {
        self.arena.text("_")
    }
}
