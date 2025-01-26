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
pub enum CompilerBuiltin {
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

impl Display for CompilerBuiltin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Compiler intrinsics for the i32 type.
            CompilerBuiltin::IntegerAdd => write!(f, "@@builtin_i32_add"),
            CompilerBuiltin::IntegerSub => write!(f, "@@builtin_i32_sub"),
            CompilerBuiltin::IntegerMul => write!(f, "@@builtin_i32_mul"),
            CompilerBuiltin::IntegerDiv => write!(f, "@@builtin_i32_div"),
            CompilerBuiltin::IntegerRem => write!(f, "@@builtin_i32_rem"),
            CompilerBuiltin::IntegerEq => write!(f, "@@builtin_i32_eq"),
            CompilerBuiltin::IntegerNeq => write!(f, "@@builtin_i32_neq"),
            CompilerBuiltin::IntegerLt => write!(f, "@builtin_i32_lt"),
            CompilerBuiltin::IntegerGt => write!(f, "@@builtin_i32_gt"),
            CompilerBuiltin::IntegerLte => write!(f, "@@builtin_i32_lte"),
            CompilerBuiltin::IntegerGte => write!(f, "@@builtin_i32_gte"),
            CompilerBuiltin::IntegerAnd => write!(f, "@@builtin_i32_and"),
            CompilerBuiltin::IntegerOr => write!(f, "@@builtin_i32_or"),
            CompilerBuiltin::IntegerNeg => write!(f, "@@builtin_i32_neg"),
            // Compiler intrinsics for the bool type.
            CompilerBuiltin::BooleanAnd => write!(f, "@@builtin_bool_and"),
            CompilerBuiltin::BooleanOr => write!(f, "@@builtin_bool_or"),
            CompilerBuiltin::BooleanNot => write!(f, "@@builtin_bool_not"),
            CompilerBuiltin::BooleanEq => write!(f, "@@builtin_bool_eq"),
            CompilerBuiltin::BooleanNeq => write!(f, "@@builtin_bool_neq"),
        }
    }
}
