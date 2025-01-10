use eight_syntax::lexer::Lexer;
use eight_syntax::parser::Parser;
use insta::assert_ron_snapshot;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut lexer = Lexer::new(&input);
        let mut parser = Parser::new(&mut lexer);
        let translation_unit = parser
            .parse()
            .expect("failed to parse corpus file into ast");
        assert_ron_snapshot!(translation_unit);
    })
}
