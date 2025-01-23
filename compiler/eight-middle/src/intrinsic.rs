//! Utilities for built-in compiler intrinsics.

use crate::hir::HirTy;
use crate::hir::{HirBinaryOp, HirBinaryOpExpr, HirUnaryOp, HirUnaryOpExpr};

/// A binary operator that is to be lowered using compiler intrinsics.
#[derive(Debug)]
pub enum BinaryIntrinsicCandidate {
    IntegerAdd,
    IntegerSub,
    IntegerMul,
    IntegerDiv,
    IntegerRem,
    IntegerEq,
    IntegerNeq,
    IntegerLt,
    IntegerGt,
    IntegerLte,
    IntegerGte,
    IntegerAnd,
    IntegerOr,
    BooleanAnd,
    BooleanOr,
    BooleanEq,
    BooleanNeq,
}

/// A unary operator that is to be lowered using compiler intrinsics.
#[derive(Debug)]
pub enum UnaryIntrinsicCandidate {
    IntegerNeg,
    BooleanNot,
}

impl HirBinaryOpExpr<'_> {
    /// Determine if a binary operator expression is an intrinsic.
    ///
    /// Calling this function is only safe once the expression has passed the type checker. Its
    /// output is meaningless before type checking.
    #[rustfmt::skip]
    pub fn is_implemented_as_intrinsic(expr: &HirBinaryOpExpr<'_>) -> Option<BinaryIntrinsicCandidate> {
        match (&expr.op, expr.lhs.ty(), expr.rhs.ty()) {
            // Built-in intrinsics for i32
            (HirBinaryOp::Add, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerAdd),
            (HirBinaryOp::Sub, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerSub),
            (HirBinaryOp::Mul, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerMul),
            (HirBinaryOp::Div, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerDiv),
            (HirBinaryOp::Rem, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerRem),
            (HirBinaryOp::Eq, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerEq),
            (HirBinaryOp::Neq, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerNeq),
            (HirBinaryOp::Lt, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerLt),
            (HirBinaryOp::Gt, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerGt),
            (HirBinaryOp::Lte, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerLte),
            (HirBinaryOp::Gte, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerGte),
            (HirBinaryOp::And, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerAnd),
            (HirBinaryOp::Or, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(BinaryIntrinsicCandidate::IntegerOr),
            // Built-in intrinsics for bool
            (HirBinaryOp::And, HirTy::Boolean(_), HirTy::Boolean(_)) => Some(BinaryIntrinsicCandidate::BooleanAnd),
            (HirBinaryOp::Or, HirTy::Boolean(_), HirTy::Boolean(_)) => Some(BinaryIntrinsicCandidate::BooleanOr),
            // This is not a binary operator that compiles to an intrinsic
            _ => None,
        }
    }
}

impl HirUnaryOpExpr<'_> {
    /// Determine if a unary operator expression is an intrinsic.
    ///
    /// Calling this function is only safe once the expression has passed the type checker. Its
    /// output is meaningless before type checking.
    #[rustfmt::skip]
    pub fn is_implemented_as_intrinsic(expr: &HirUnaryOpExpr<'_>) -> Option<UnaryIntrinsicCandidate> {
        match (&expr.op, expr.operand.ty()) {
            // Built-in intrinsics for i32
            (HirUnaryOp::Neg, HirTy::Integer32(_)) => Some(UnaryIntrinsicCandidate::IntegerNeg),
            // Built-in intrinsics for bool
            (HirUnaryOp::Not, HirTy::Boolean(_)) => Some(UnaryIntrinsicCandidate::BooleanNot),
            // This is not a unary operator that compiles to an intrinsic
            _ => None,
        }
    }
}
