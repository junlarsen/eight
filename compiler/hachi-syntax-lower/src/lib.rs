mod error;
mod expr;
mod item;
mod stmt;
mod r#type;

use hachi_syntax::ForStmt;
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
pub struct SyntaxLoweringPass<'ast> {
    loop_depth: VecDeque<&'ast ForStmt>,
}

impl SyntaxLoweringPass<'_> {
    pub fn new() -> Self {
        Self {
            loop_depth: VecDeque::new(),
        }
    }
}

impl Default for SyntaxLoweringPass<'_> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::SyntaxLoweringPass;
    use hachi_macros::{assert_err, assert_ok};

    macro_rules! assert_lower_err {
        ($input:expr) => {{
            let mut lexer = hachi_syntax::Lexer::new($input);
            let mut parser = hachi_syntax::Parser::new(&mut lexer);
            let translation_unit = assert_ok!(parser.parse());
            let mut lowering_pass = SyntaxLoweringPass::new();
            assert_err!(lowering_pass.visit_translation_unit(&translation_unit));
        }};
    }

    macro_rules! assert_lower_ok {
        ($input:expr) => {{
            let mut lexer = hachi_syntax::Lexer::new($input);
            let mut parser = hachi_syntax::Parser::new(&mut lexer);
            let translation_unit = assert_ok!(parser.parse());
            let mut lowering_pass = SyntaxLoweringPass::new();
            assert_ok!(lowering_pass.visit_translation_unit(&translation_unit))
        }};
    }

    #[test]
    fn test_break_outside_loop_diagnostic() {
        assert_lower_err!(
            r#"
        fn foo() {
          break;
        }
        "#
        );
        assert_lower_ok!(
            r#"
        fn foo() {
          for (let i = 0; i < 10; i = i + 1) {
            break;
          }
        }
        "#
        );
        assert_lower_ok!(
            r#"
        fn foo() {
          for (;;) {
            break;
            for (let i = 0; i < 10; i = i + 1) {
              break;
            }
            break;
          }
        }
        "#
        );
    }

    #[test]
    fn test_continue_outside_loop_diagnostic() {
        assert_lower_err!(
            r#"
        fn foo() {
          continue;
        }
        "#
        );
        assert_lower_ok!(
            r#"
        fn foo() {
          for (let i = 0; i < 10; i = i + 1) {
            continue;
          }
        }
        "#
        );
        assert_lower_ok!(
            r#"
        fn foo() {
          for (;;) {
            continue;
            for (let i = 0; i < 10; i = i + 1) {
              continue;
            }
          }
        }
        "#
        );
    }
}
