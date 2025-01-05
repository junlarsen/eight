use bumpalo::Bump;
use hachi_hir::passes::{
    ASTSyntaxLoweringPass, HirModuleDebugPass, HirModuleTypeCheckerPass, TypingContext,
};
use hachi_hir::ty::HirTyArena;

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
        let mut lexer = hachi_syntax::Lexer::new(source.as_ref());
        let mut parser = hachi_syntax::Parser::new(&mut lexer);

        let bump = Bump::new();
        let arena = HirTyArena::new(&bump);

        let mut lowering_pass = ASTSyntaxLoweringPass::new(&arena);
        let tu = parser.parse()?;
        let mut module = lowering_pass.visit_translation_unit(&tu)?;
        let mut cx = TypingContext::new(&arena);
        HirModuleTypeCheckerPass::visit(&mut module, &mut cx)?;
        if self.options.emit_ast {
            let syntax = ron::ser::to_string_pretty(&tu, Default::default())
                .expect("failed to serialize ast to ron");
            println!("{}", syntax);
        }
        if self.options.emit_hir {
            let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
            println!("{}", doc);
        }
        Ok(())
    }
}
