use hachi_hir::format::HirModuleFormatter;

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
        let mut lowering_pass = hachi_hir::syntax_lowering::SyntaxLoweringPass::new();
        let tu = parser.parse()?;
        let module = lowering_pass.visit_translation_unit(&tu)?;
        if self.options.emit_ast {
            let syntax = ron::ser::to_string_pretty(&tu, Default::default())
                .expect("failed to serialize ast to ron");
            println!("{}", syntax);
        }
        if self.options.emit_hir {
            let doc = HirModuleFormatter::format_hir_module(&module);
            let mut w = Vec::new();
            doc.render(80, &mut w).expect("failed to render doc");
            println!("{}", String::from_utf8(w).unwrap());
        }
        Ok(())
    }
}
