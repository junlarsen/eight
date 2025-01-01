use hachi_hir::format::HirModuleFormatter;
use hachi_hir::syntax_lowering::SyntaxLoweringPass;
use hachi_syntax::Lexer;
use hachi_syntax::Parser;
use insta::assert_snapshot;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut lexer = Lexer::new(&input);
        let mut parser = Parser::new(&mut lexer);
        let translation_unit = parser
            .parse()
            .unwrap_or_else(|_| panic!("failed to parse corpus file {} into ast", path.display()));
        let mut lowering_pass = SyntaxLoweringPass::new();
        let module = lowering_pass
            .visit_translation_unit(&translation_unit)
            .expect("failed to lower translation unit");
        let doc = HirModuleFormatter::format_hir_module_to_string(&module);
        assert_snapshot!(doc);
    })
}
