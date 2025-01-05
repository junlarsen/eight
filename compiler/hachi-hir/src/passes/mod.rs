mod debug;
mod syntax_lower;
mod type_checker;

pub use debug::HirModuleDebugPass;
pub use syntax_lower::ASTSyntaxLoweringPass;
pub use type_checker::{HirModuleTypeCheckerPass, TypingContext};
