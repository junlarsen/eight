//! Utilities for built-in compiler functions.

use crate::context::CompileContext;
use crate::hir::HirTy;
use std::fmt::Display;

/// A binary operator that is to be lowered using compiler intrinsics.
///
/// Compiler intrinsics are prefixed with `@@` and are not actual symbols that the user can create
/// or call directly.
///
/// Specific code is lowered into compiler intrinsics when the compiler detects that some code
/// corresponds to a specific pattern. For example, all built-in operators on types like i32 are
/// implemented as compiler intrinsics, and lowered into instructions like `arith.add` instead of
/// function calls.
#[derive(Debug)]
pub enum CompilerIntrinsic {
    IntegerAdd,
    IntegerSub,
    IntegerMul,
    IntegerDiv,
    IntegerRem,
    IntegerEq,
    IntegerNeq,
    IntegerLt,
    IntegerGt,
    IntegerLe,
    IntegerGe,
    BooleanAnd,
    BooleanOr,
    BooleanEq,
    BooleanNeq,
    IntegerNeg,
    BooleanNot,
}

impl<'hir> CompilerIntrinsic {
    pub fn get_application_type(&self, cc: &'hir CompileContext<'hir>) -> &'hir HirTy<'hir> {
        match self {
            // Intrinsics of type fn(i32, i32) -> i32
            CompilerIntrinsic::IntegerAdd
            | CompilerIntrinsic::IntegerSub
            | CompilerIntrinsic::IntegerMul
            | CompilerIntrinsic::IntegerDiv
            | CompilerIntrinsic::IntegerRem => cc.hir_function_type(
                cc.hir_integer32_type(),
                vec![cc.hir_integer32_type(), cc.hir_integer32_type()],
            ),
            // Intrinsics of type fn(i32, i32) -> bool
            CompilerIntrinsic::IntegerEq
            | CompilerIntrinsic::IntegerNeq
            | CompilerIntrinsic::IntegerLt
            | CompilerIntrinsic::IntegerGt
            | CompilerIntrinsic::IntegerLe
            | CompilerIntrinsic::IntegerGe => cc.hir_function_type(
                cc.hir_boolean_type(),
                vec![cc.hir_integer32_type(), cc.hir_integer32_type()],
            ),
            // Intrinsics of type fn(bool, bool) -> bool
            CompilerIntrinsic::BooleanAnd
            | CompilerIntrinsic::BooleanOr
            | CompilerIntrinsic::BooleanEq
            | CompilerIntrinsic::BooleanNeq => cc.hir_function_type(
                cc.hir_boolean_type(),
                vec![cc.hir_boolean_type(), cc.hir_boolean_type()],
            ),
            // Intrinsics of type fn(i32) -> i32
            CompilerIntrinsic::IntegerNeg => {
                cc.hir_function_type(cc.hir_integer32_type(), vec![cc.hir_integer32_type()])
            }
            // Intrinsics of type fn(bool) -> bool
            CompilerIntrinsic::BooleanNot => {
                cc.hir_function_type(cc.hir_boolean_type(), vec![cc.hir_boolean_type()])
            }
        }
    }
}

impl Display for CompilerIntrinsic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Compiler intrinsics for the i32 type.
            CompilerIntrinsic::IntegerAdd => write!(f, "@@builtin_i32_add"),
            CompilerIntrinsic::IntegerSub => write!(f, "@@builtin_i32_sub"),
            CompilerIntrinsic::IntegerMul => write!(f, "@@builtin_i32_mul"),
            CompilerIntrinsic::IntegerDiv => write!(f, "@@builtin_i32_div"),
            CompilerIntrinsic::IntegerRem => write!(f, "@@builtin_i32_rem"),
            CompilerIntrinsic::IntegerEq => write!(f, "@@builtin_i32_eq"),
            CompilerIntrinsic::IntegerNeq => write!(f, "@@builtin_i32_neq"),
            CompilerIntrinsic::IntegerLt => write!(f, "@@builtin_i32_lt"),
            CompilerIntrinsic::IntegerGt => write!(f, "@@builtin_i32_gt"),
            CompilerIntrinsic::IntegerLe => write!(f, "@@builtin_i32_le"),
            CompilerIntrinsic::IntegerGe => write!(f, "@@builtin_i32_ge"),
            CompilerIntrinsic::IntegerNeg => write!(f, "@@builtin_i32_neg"),
            // Compiler intrinsics for the bool type.
            CompilerIntrinsic::BooleanAnd => write!(f, "@@builtin_bool_and"),
            CompilerIntrinsic::BooleanOr => write!(f, "@@builtin_bool_or"),
            CompilerIntrinsic::BooleanNot => write!(f, "@@builtin_bool_not"),
            CompilerIntrinsic::BooleanEq => write!(f, "@@builtin_bool_eq"),
            CompilerIntrinsic::BooleanNeq => write!(f, "@@builtin_bool_neq"),
        }
    }
}
