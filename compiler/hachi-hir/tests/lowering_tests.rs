use hachi_hir::passes::HirModuleDebugPass;

mod common;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/lowering/*.test", |path| {
        let input = std::fs::read_to_string(path).expect("failed to read input file");
        assert_hir_module_compiles!(&input);
    })
}
