mod error;
mod expr;
mod item;
mod stmt;
mod r#type;

use std::collections::VecDeque;

/// Translation pass that lowers the `hachi-syntax` AST into the HIR representation.
///
/// This pass is responsible for lowering syntactic sugar into the HIR nodes. It also does some very
/// basic semantic analysis, such as checking `return` and `break`/`continue` statement contexts.
///
/// All types (note: generic types too) are preserved, meaning that a generic type like `T` will be
/// lowered into a TConst type, despite the fact that the type checker will replace this with a
/// fresh type variable.
///
/// TODO: Do we one-shot the type-checker here?
#[derive(Debug)]
pub struct SyntaxLoweringPass {
    loop_depth: VecDeque<bool>,
    function_depth: VecDeque<bool>,
}

impl SyntaxLoweringPass {
    pub fn new() -> Self {
        Self {
            loop_depth: VecDeque::new(),
            function_depth: VecDeque::new(),
        }
    }
}

impl Default for SyntaxLoweringPass {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {}
