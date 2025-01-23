//! Utilities for built-in compiler intrinsics.

use crate::hir::HirTy;
use crate::hir::{HirBinaryOp, HirBinaryOpExpr, HirUnaryOp, HirUnaryOpExpr};
use std::fmt::Display;

/// A binary operator that is to be lowered using compiler intrinsics.
#[derive(Debug)]
pub enum IntrinsicCandidate {
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
    IntegerNeg,
    BooleanNot,
}

impl Display for IntrinsicCandidate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntrinsicCandidate::IntegerAdd => write!(f, "__builtin_iadd"),
            IntrinsicCandidate::IntegerSub => write!(f, "__builtin_isub"),
            IntrinsicCandidate::IntegerMul => write!(f, "__builtin_imul"),
            IntrinsicCandidate::IntegerDiv => write!(f, "__builtin_idiv"),
            IntrinsicCandidate::IntegerRem => write!(f, "__builtin_irem"),
            IntrinsicCandidate::IntegerEq => write!(f, "__builtin_ieq"),
            IntrinsicCandidate::IntegerNeq => write!(f, "__builtin_ineq"),
            IntrinsicCandidate::IntegerLt => write!(f, "__builtin_ilt"),
            IntrinsicCandidate::IntegerGt => write!(f, "__builtin_igt"),
            IntrinsicCandidate::IntegerLte => write!(f, "__builtin_ilte"),
            IntrinsicCandidate::IntegerGte => write!(f, "__builtin_igte"),
            IntrinsicCandidate::IntegerAnd => write!(f, "__builtin_iand"),
            IntrinsicCandidate::IntegerOr => write!(f, "__builtin_ior"),
            IntrinsicCandidate::BooleanAnd => write!(f, "__builtin_and"),
            IntrinsicCandidate::BooleanOr => write!(f, "__builtin_or"),
            IntrinsicCandidate::BooleanEq => write!(f, "__builtin_eq"),
            IntrinsicCandidate::BooleanNeq => write!(f, "__builtin_neq"),
            IntrinsicCandidate::IntegerNeg => write!(f, "__builtin_neg"),
            IntrinsicCandidate::BooleanNot => write!(f, "__builtin_not"),
        }
    }
}

impl HirBinaryOpExpr<'_> {
    /// Determine if a binary operator expression is an intrinsic.
    ///
    /// Calling this function is only safe once the expression has passed the type checker. Its
    /// output is meaningless before type checking.
    #[rustfmt::skip]
    pub fn is_implemented_as_intrinsic(expr: &HirBinaryOpExpr<'_>) -> Option<IntrinsicCandidate> {
        match (&expr.op, expr.lhs.ty(), expr.rhs.ty()) {
            // Built-in intrinsics for i32
            (HirBinaryOp::Add, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerAdd),
            (HirBinaryOp::Sub, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerSub),
            (HirBinaryOp::Mul, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerMul),
            (HirBinaryOp::Div, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerDiv),
            (HirBinaryOp::Rem, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerRem),
            (HirBinaryOp::Eq, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerEq),
            (HirBinaryOp::Neq, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerNeq),
            (HirBinaryOp::Lt, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerLt),
            (HirBinaryOp::Gt, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerGt),
            (HirBinaryOp::Lte, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerLte),
            (HirBinaryOp::Gte, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerGte),
            (HirBinaryOp::And, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerAnd),
            (HirBinaryOp::Or, HirTy::Integer32(_), HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerOr),
            // Built-in intrinsics for bool
            (HirBinaryOp::And, HirTy::Boolean(_), HirTy::Boolean(_)) => Some(IntrinsicCandidate::BooleanAnd),
            (HirBinaryOp::Or, HirTy::Boolean(_), HirTy::Boolean(_)) => Some(IntrinsicCandidate::BooleanOr),
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
    pub fn is_implemented_as_intrinsic(expr: &HirUnaryOpExpr<'_>) -> Option<IntrinsicCandidate> {
        match (&expr.op, expr.operand.ty()) {
            // Built-in intrinsics for i32
            (HirUnaryOp::Neg, HirTy::Integer32(_)) => Some(IntrinsicCandidate::IntegerNeg),
            // Built-in intrinsics for bool
            (HirUnaryOp::Not, HirTy::Boolean(_)) => Some(IntrinsicCandidate::BooleanNot),
            // This is not a unary operator that compiles to an intrinsic
            _ => None,
        }
    }
}
