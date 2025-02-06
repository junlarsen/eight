//! Utilities for built-in compiler functions.

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
    IntegerLte,
    IntegerGte,
    BooleanAnd,
    BooleanOr,
    BooleanEq,
    BooleanNeq,
    IntegerNeg,
    BooleanNot,
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
            CompilerIntrinsic::IntegerLt => write!(f, "@builtin_i32_lt"),
            CompilerIntrinsic::IntegerGt => write!(f, "@@builtin_i32_gt"),
            CompilerIntrinsic::IntegerLte => write!(f, "@@builtin_i32_lte"),
            CompilerIntrinsic::IntegerGte => write!(f, "@@builtin_i32_gte"),
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
