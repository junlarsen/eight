use hachi_parse::lexer::Lexer;
use hachi_parse::parser::Parser;
use insta::assert_ron_snapshot;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut parser = Parser::new(Lexer::new(&input));
        let translation_unit = parser
            .parse()
            .expect(format!("failed to parse corpus file {} into ast", path.display()).as_str());
        assert_ron_snapshot!(*translation_unit);
    })
}
