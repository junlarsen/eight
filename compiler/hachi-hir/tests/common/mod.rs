/// A macro for building a HIR module from source code, and asserting that the syntax tree for the
/// module can be lowered into HIR.
#[macro_export]
macro_rules! assert_hir_module_compiles {
    ($input:expr) => {{
        use hachi_hir::syntax_lowering::SyntaxLoweringPass;
        use hachi_syntax::Lexer;
        use hachi_syntax::Parser;

        let mut lexer = Lexer::new($input);
        let mut parser = Parser::new(&mut lexer);
        let translation_unit = parser
            .parse()
            .unwrap_or_else(|_| panic!("failed to parse corpus file into syntax tree"));
        let mut lowering_pass = SyntaxLoweringPass::new();
        let module = lowering_pass
            .visit_translation_unit(&translation_unit)
            .expect("failed to lower translation unit");
        module
    }};
}
