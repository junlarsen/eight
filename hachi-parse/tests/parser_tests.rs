use hachi_parse::Lexer;
use hachi_parse::Parser;
use insta::assert_ron_snapshot;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut parser = Parser::new(Lexer::new(&input));
        let translation_unit = parser
            .parse()
            .unwrap_or_else(|_| panic!("failed to parse corpus file {} into ast", path.display()));
        assert_ron_snapshot!(*translation_unit);
    })
}
