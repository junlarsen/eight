use hachi_hir::format::HirModuleFormatter;
use hachi_hir::passes::type_checker::TypeChecker;
use insta::assert_snapshot;

mod common;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/inference/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let mut module = assert_hir_module_compiles!(&input);
        TypeChecker::visit(&mut module).expect("failed to type check corpus file");
        let doc = HirModuleFormatter::format_hir_module_to_string(&module);
        assert_snapshot!(doc);
    })
}
