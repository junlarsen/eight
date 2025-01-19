//! High-level Intermediate Representation.
//!
//! The High-level IR is a fully-typed, easily hackable representation of the source code. It is
//! designed to be easy to mutate and replace. It is directly derived from the syntax tree, and uses
//! the common types defined in the `ty` module for type checking and inference.
//!
//! The HIR is a concrete representation of the program (not the source code). It has all the sugar
//! and abstractions that the syntax of the language provides, providing more information about the
//! program than the AST.

use crate::error::HirError;
use eight_middle::hir::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirDerefExpr,
    HirExpr, HirGroupExpr, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp,
    HirUnaryOpExpr,
};
use eight_middle::hir::item::{HirFunction, HirInstance, HirTrait};
use eight_middle::hir::signature::{HirFunctionSignature, HirInstanceSignature, HirTraitSignature};
use eight_middle::hir::stmt::{
    HirBlockStmt, HirBreakStmt, HirContinueStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt,
    HirReturnStmt, HirStmt,
};
use eight_middle::hir::ty::HirTy;
use eight_middle::LinkageType;
use eight_span::Span;
use std::collections::BTreeMap;

pub mod arena;
pub mod error;
pub mod query;
pub mod syntax_lowering_pass;
pub mod textual_pass;
pub mod type_check_pass;

/// A HIR node builder.
///
/// The purpose of the HIR builder is to provide API-stable ways to build HIR nodes. Because the
/// internal representation of the nodes isn't.
///
/// TODO: Build signatures and types here as well.
pub struct HirBuilder;

impl<'hir> HirBuilder {
    /// Utility function to build a vector from an iterator.
    ///
    /// This saves us from having to write `.iter().map(|x| ...).collect()` every time we want to
    /// collect something into a vector.
    pub fn build_vec<A, B>(
        iter: impl IntoIterator<Item = A>,
        f: impl FnMut(A) -> Result<B, HirError>,
    ) -> Result<Vec<B>, HirError> {
        iter.into_iter().map(f).collect()
    }

    /// Build a HIR function.
    pub fn build_function(
        span: Span,
        name: &'hir str,
        name_span: Span,
        signature: &'hir HirFunctionSignature<'hir>,
        body: Vec<HirStmt<'hir>>,
        linkage_type: LinkageType,
    ) -> HirFunction<'hir> {
        HirFunction {
            span,
            name,
            name_span,
            signature,
            body,
            linkage_type,
            type_parameter_substitutions: BTreeMap::new(),
            instantiated_parameters: BTreeMap::new(),
            instantiated_return_type: None,
        }
    }

    /// Build a HIR trait.
    pub fn build_trait(
        span: Span,
        name: &'hir str,
        name_span: Span,
        signature: &'hir HirTraitSignature<'hir>,
    ) -> HirTrait<'hir> {
        HirTrait {
            span,
            name,
            name_span,
            signature,
        }
    }

    /// Build a HIR instance.
    pub fn build_instance(
        span: Span,
        name: &'hir str,
        name_span: Span,
        type_arguments: Vec<&'hir HirTy<'hir>>,
        members: Vec<HirFunction<'hir>>,
        signature: &'hir HirInstanceSignature<'hir>,
    ) -> HirInstance<'hir> {
        HirInstance {
            span,
            name,
            name_span,
            type_arguments,
            members,
            signature,
            type_parameter_substitutions: BTreeMap::new(),
        }
    }

    /// Build a HIR let statement.
    pub fn build_let_stmt(
        span: Span,
        name: &'hir str,
        name_span: Span,
        ty: &'hir HirTy<'hir>,
        type_annotation: Option<Span>,
        value: HirExpr<'hir>,
    ) -> HirLetStmt<'hir> {
        HirLetStmt {
            span,
            name,
            name_span,
            ty,
            type_annotation,
            value,
        }
    }

    /// Build a HIR loop statement.
    pub fn build_loop_stmt(
        span: Span,
        condition: HirExpr<'hir>,
        body: Vec<HirStmt<'hir>>,
    ) -> HirLoopStmt<'hir> {
        HirLoopStmt {
            span,
            condition,
            body,
        }
    }

    /// Build a HIR block statement.
    pub fn build_block_stmt(span: Span, body: Vec<HirStmt<'hir>>) -> HirBlockStmt<'hir> {
        HirBlockStmt { span, body }
    }

    /// Build a HIR return statement.
    pub fn build_return_stmt(span: Span, value: Option<HirExpr<'hir>>) -> HirReturnStmt<'hir> {
        HirReturnStmt { span, value }
    }

    /// Build an HIR if statement.
    pub fn build_if_stmt(
        span: Span,
        condition: HirExpr<'hir>,
        happy_path: Vec<HirStmt<'hir>>,
        unhappy_path: Vec<HirStmt<'hir>>,
    ) -> HirIfStmt<'hir> {
        HirIfStmt {
            span,
            condition,
            happy_path,
            unhappy_path,
        }
    }

    /// Build a break statement.
    pub fn build_break_stmt(span: Span) -> HirBreakStmt {
        HirBreakStmt { span }
    }

    /// Build a continue statement.
    pub fn build_continue_stmt(span: Span) -> HirContinueStmt {
        HirContinueStmt { span }
    }

    pub fn build_expr_stmt(span: Span, expr: HirExpr<'hir>) -> HirExprStmt<'hir> {
        HirExprStmt { span, expr }
    }

    /// Build an assignment expression.
    pub fn build_assign_expr(
        span: Span,
        lhs: HirExpr<'hir>,
        rhs: HirExpr<'hir>,
        ty: &'hir HirTy<'hir>,
    ) -> HirAssignExpr<'hir> {
        HirAssignExpr {
            span,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            ty,
        }
    }

    /// Build a call expression.
    pub fn build_call_expr(
        span: Span,
        callee: HirExpr<'hir>,
        arguments: Vec<HirExpr<'hir>>,
        type_arguments: Vec<&'hir HirTy<'hir>>,
        ty: &'hir HirTy<'hir>,
    ) -> HirCallExpr<'hir> {
        HirCallExpr {
            span,
            callee: Box::new(callee),
            arguments,
            type_arguments,
            ty,
        }
    }

    /// Build a construct expression.
    pub fn build_construct_expr(
        span: Span,
        callee: &'hir HirTy<'hir>,
        arguments: Vec<HirConstructExprArgument<'hir>>,
        ty: &'hir HirTy<'hir>,
    ) -> HirConstructExpr<'hir> {
        HirConstructExpr {
            span,
            callee,
            arguments,
            ty,
        }
    }

    /// Build a construct expression argument.
    pub fn build_construct_expr_argument(
        span: Span,
        field: &'hir str,
        field_span: Span,
        expr: HirExpr<'hir>,
    ) -> HirConstructExprArgument<'hir> {
        HirConstructExprArgument {
            span,
            field,
            field_span,
            expr: Box::new(expr),
        }
    }

    /// Build a group expression
    pub fn build_group_expr(
        span: Span,
        inner: HirExpr<'hir>,
        ty: &'hir HirTy<'hir>,
    ) -> HirGroupExpr<'hir> {
        HirGroupExpr {
            span,
            inner: Box::new(inner),
            ty,
        }
    }

    /// Build a reference expression
    pub fn build_integer_literal_expr(
        span: Span,
        value: i32,
        ty: &'hir HirTy<'hir>,
    ) -> HirIntegerLiteralExpr<'hir> {
        HirIntegerLiteralExpr { span, value, ty }
    }

    /// Build a boolean literal expression
    pub fn build_boolean_literal_expr(
        span: Span,
        value: bool,
        ty: &'hir HirTy<'hir>,
    ) -> HirBooleanLiteralExpr<'hir> {
        HirBooleanLiteralExpr { span, value, ty }
    }

    /// Build a unary operation expression
    pub fn build_unary_op_expr(
        span: Span,
        operand: HirExpr<'hir>,
        op: HirUnaryOp,
        op_span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirUnaryOpExpr<'hir> {
        HirUnaryOpExpr {
            span,
            operand: Box::new(operand),
            op,
            op_span,
            ty,
        }
    }

    /// Build a deref expression
    pub fn build_deref_expr(
        span: Span,
        inner: HirExpr<'hir>,
        ty: &'hir HirTy<'hir>,
    ) -> HirDerefExpr<'hir> {
        HirDerefExpr {
            span,
            inner: Box::new(inner),
            ty,
        }
    }

    /// Build an address of expression
    pub fn build_address_of_expr(
        span: Span,
        inner: HirExpr<'hir>,
        ty: &'hir HirTy<'hir>,
    ) -> HirAddressOfExpr<'hir> {
        HirAddressOfExpr {
            span,
            inner: Box::new(inner),
            ty,
        }
    }

    /// Build a binary operation expression
    pub fn build_binary_op_expr(
        span: Span,
        lhs: HirExpr<'hir>,
        rhs: HirExpr<'hir>,
        op: HirBinaryOp,
        op_span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirBinaryOpExpr<'hir> {
        HirBinaryOpExpr {
            span,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
            op,
            op_span,
            ty,
        }
    }

    /// Build a constant index expression
    pub fn build_constant_index_expr(
        span: Span,
        origin: HirExpr<'hir>,
        index: &'hir str,
        index_span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirConstantIndexExpr<'hir> {
        HirConstantIndexExpr {
            span,
            origin: Box::new(origin),
            index,
            index_span,
            ty,
        }
    }

    /// Build an offset index expression
    pub fn build_offset_index_expr(
        span: Span,
        origin: HirExpr<'hir>,
        index: HirExpr<'hir>,
        ty: &'hir HirTy<'hir>,
    ) -> HirOffsetIndexExpr<'hir> {
        HirOffsetIndexExpr {
            span,
            origin: Box::new(origin),
            index: Box::new(index),
            ty,
        }
    }

    pub fn build_reference_expr(
        span: Span,
        name: &'hir str,
        name_span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirReferenceExpr<'hir> {
        HirReferenceExpr {
            span,
            name,
            name_span,
            ty,
            is_reference_to_function: false,
        }
    }
}
