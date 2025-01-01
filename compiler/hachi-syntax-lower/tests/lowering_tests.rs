use hachi_syntax::Lexer;
use hachi_syntax::Parser;
use hachi_syntax_lower::SyntaxLoweringPass;
use insta::assert_ron_snapshot;

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
        let module = lowering_pass.visit_translation_unit(&translation_unit).unwrap();
        assert_ron_snapshot!(module);
    })
}
