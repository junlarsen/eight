use bumpalo::Bump;
use eight_syntax::arena::AstArena;
use eight_syntax::lexer::Lexer;
use eight_syntax::parser::Parser;
use insta::assert_ron_snapshot;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut lexer = Lexer::new(&input);
        let bump = Bump::new();
        let arena = AstArena::new(&bump);
        let mut parser = Parser::new(&mut lexer, &arena);
        let translation_unit = parser
            .parse()
            .expect("failed to parse corpus file into ast");
        assert_ron_snapshot!(translation_unit);
    })
}
