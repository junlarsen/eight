//! Intermediate representation for programs.
//!
//! The IR is a simplified representation of the source language. We base on SSA-form which only
//! allows for single assignment.
//!
//! Note that the IR does not truly have a textual form, but as a simplified example of how the
//! hierarchy of the types could look like, we can write the following
//! (compiled for a 64-bit system, where pointer size = 8):
//!
//! ```text
//! module {
//!   type Matrix = { r: i32, c: i32, buf: ptr };
//!   fn @matrix_matrix_multiply(%1: Matrix, %2: Matrix) -> Matrix {
//!     entry:
//!       %c = mem.alloc 16
//!       %c_r = mem.load %1, 0
//!       %c_c = mem.load %2, 1
//!       mem.store %c, 0, %c_r
//!       mem.store %c, 4, %c_c
//!       %buf_item_size = const.i32 4
//!       %buf_size_0 = mul.i32 %c_r, %c_c
//!       %buf_size_1 = mul.i32 %buf_size_0, %buf_item_size
//!       %buf = call malloc(%buf_size_1)
//!       mem.store %c, 8, %buf
//!       branch loop_i_header
//!     loop_i_header:
//!       %i_init = const.i32 0
//!       %i = mem.alloc 4
//!       mem.store %i, 0, %i_init
//!       branch @loop_i_cond
//!     loop_i_cond:
//!       %i = mem.load %i, 0
//!       %i_cmp = cmp.lt.i32 %i, %c_r
//!       branch.cond %i_cmp, @loop_i_body, @loop_i_exit
//!     loop_i_body:
//!       branch loop_j_header
//!     loop_j_header:
//!       %j_init = const.i32 0
//!       %j = mem.alloc 4
//!       mem.store %j, 0, %j_init
//!       branch loop_j_cond
//!     loop_j_cond:
//!       %j = mem.load %j, 0
//!       %j_cmp = cmp.lt.i32 %j, %c_c
//!       branch.cond %j_cmp, loop_j_body_0, loop_j_exit
//!     loop_j_body_0:
//!       %sum = const.i32 0
//!       branch loop_k_header
//!     loop_k_header:
//!       %k_init = const.i32 0
//!       %k = mem.alloc 4
//!       mem.store %k, 0, %k_init
//!       branch loop_k_cond
//!     loop_k_cond:
//!       %k = mem.load %k, 0
//!       %k_cmp = cmp.lt.i32 %k, %c_c
//!       branch.cond %k_cmp, loop_k_body, loop_k_exit
//!     loop_k_body:
//!       %f = mem.load %sum, 0
//!       %a_idx_0 = mul.i32 %i, %c_c
//!       %a_idx_1 = add.i32 %a_idx_0, %k
//!       %a = mem.load %buf, mul.i32(%i, %c_c)
//!       %b_idx_0 = mul.i32 %j, %c_c
//!       %b_idx_1 = add.i32 %b_idx_0, %k
//!       %b = mem.load %buf, mul.i32(%j, %c_c)
//!       %mul = mul.i32 %a, %b
//!       %sum = add.i32 %sum, %mul
//!       mem.store %sum, 0, %f
//!       branch loop_k_exit
//!     loop_k_continue:
//!       %k = mem.load %k, 0
//!       %k_inc = add.i32 %k, 1
//!       mem.store %k, 0, %k_inc
//!       branch loop_k_header
//!     loop_j_continue:
//!       %j = mem.load %j, 0
//!       %j_inc = add.i32 %j, 1
//!       mem.store %j, 0, %j_inc
//!       branch loop_j_header
//!     loop_i_continue:
//!       %i = mem.load %i, 0
//!       %i_inc = add.i32 %i, 1
//!       mem.store %i, 0, %i_inc
//!       branch loop_i_header
//!     loop_i_exit:
//!       branch exit
//!     loop_j_exit:
//!       branch loop_i_continue
//!     loop_k_exit:
//!       %c_idx_0 = mul.i32 %i, %c_c
//!       %c_idx_1 = add.i32 %c_idx_0, %j
//!       %sum_0 = mem.load %sum, 0
//!       mem.store %c, %c_idx_1, %sum_0
//!       branch loop_j_continue
//!     exit:
//!       %c = mem.load %c, 0
//!       ret %c
//!   }
//! }
//! ```
//!
//! Note that as opposed to the source language, the IR uses opaque pointers to represent the
//! memory layout of the types. This is because it is not of significance to the memory layout of
//! the packed types. This also follows the design of the LLVM IR.

pub struct MirFunctionReference {}
pub struct MirConstant {}
pub struct MirLocal {}
pub struct MirLabel {}

pub enum MirType {
    Integer32,
    Unit,
    Pointer,
    Named(String),
}

pub enum MirInstruction {
    Branch(MirBranchInstruction),
    ConditionalBranch(MirConditionalBranchInstruction),
    Constant(MirConstantInstruction),
    CompareLessThan(MirCompareLessThanInstruction),
    CompareGreaterThan(MirCompareGreaterThanInstruction),
    CompareLessThanOrEqual(MirCompareLessThanOrEqualInstruction),
    CompareGreaterThanOrEqual(MirCompareGreaterThanOrEqualInstruction),
    CompareEqual(MirCompareEqualInstruction),
    CompareNotEqual(MirCompareNotEqualInstruction),
    Call(MirCallInstruction),
}

/// The `branch` instruction
pub struct MirBranchInstruction {
    pub target: MirLabel,
}

/// The `branch.cond` instruction
pub struct MirConditionalBranchInstruction {
    pub condition: MirLocal,
    pub true_target: MirLabel,
    pub false_target: MirLabel,
}

/// The `const.<type>` instruction
pub struct MirConstantInstruction {
    pub value: MirConstant,
    pub ty: MirType,
}

/// The `cmp.lt.<type>` instruction
pub struct MirCompareLessThanInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `cmp.gt.<type>` instruction
pub struct MirCompareGreaterThanInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `cmp.le.<type>` instruction
pub struct MirCompareLessThanOrEqualInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `cmp.ge.<type>` instruction
pub struct MirCompareGreaterThanOrEqualInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `cmp.eq.<type>` instruction
pub struct MirCompareEqualInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `cmp.ne.<type>` instruction
pub struct MirCompareNotEqualInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `mul.<type>` instruction
pub struct MirMultiplyInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `add.<type>` instruction
pub struct MirAddInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `sub.<type>` instruction
pub struct MirSubtractInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `load` instruction
pub struct MirDivideInstruction {
    pub lhs: MirLocal,
    pub rhs: MirLocal,
    pub ty: MirType,
}

/// The `call` instruction
pub struct MirCallInstruction {
    pub callee: MirFunctionReference,
    pub arguments: Vec<MirLocal>,
}

/// The `ret` instruction
pub struct MirReturnInstruction {
    pub value: Option<MirLocal>,
}

pub struct MirLoadInstruction {
    pub pointer: MirLocal,
    pub ty: MirType,
}

pub struct MirStoreInstruction {
    pub pointer: MirLocal,
    pub value: MirLocal,
    pub ty: MirType,
}
