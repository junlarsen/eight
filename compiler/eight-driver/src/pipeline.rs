use bumpalo::Bump;
use eight_hir::arena::HirArena;
use eight_hir::query::HirQueryDatabase;
use eight_hir::syntax_lowering_pass::ASTSyntaxLoweringPass;
use eight_hir::textual_pass::HirModuleDebugPass;
use eight_hir::type_check_pass::{HirModuleTypeCheckerPass, TypingContext};
use eight_syntax::arena::AstArena;

pub struct PipelineOptions {
    pub emit_ast: bool,
    pub emit_hir: bool,
}

pub struct Pipeline {
    options: PipelineOptions,
}

impl Pipeline {
    pub fn new(options: PipelineOptions) -> Self {
        Self { options }
    }

    pub fn run<T: AsRef<str>>(&self, source: T) -> miette::Result<()> {
        let ast_bump = Bump::new();
        let ast_arena = AstArena::new(&ast_bump);
        let mut lexer = eight_syntax::lexer::Lexer::new(source.as_ref());
        let mut parser = eight_syntax::parser::Parser::new(&mut lexer, &ast_arena);
        let tu = parser.parse()?;
        if self.options.emit_ast {
            let syntax = ron::ser::to_string_pretty(&tu, Default::default())
                .expect("failed to serialize ast to ron");
            println!("{}", syntax);
        }

        let hir_bump = Bump::new();
        let hir_arena = HirArena::new(&hir_bump);
        let lowering_pass = ASTSyntaxLoweringPass::new(&hir_arena);
        let mut module = lowering_pass.visit_translation_unit(&tu)?;
        let query_database = HirQueryDatabase::new(module.signature);
        let mut cx = TypingContext::new(&hir_arena, &query_database);
        HirModuleTypeCheckerPass::visit(&mut module, &mut cx)?;
        if self.options.emit_hir {
            let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
            println!("{}", doc);
        }
        Ok(())
    }
}
