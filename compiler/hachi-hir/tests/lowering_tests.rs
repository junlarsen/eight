use hachi_hir::passes::HirModuleDebugPass;
use insta::assert_snapshot;

mod common;

#[test]
fn test_snapshot_corpus() {
    insta::glob!("data/lowering/*.test", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let module = assert_hir_module_compiles!(&input);
        let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
        assert_snapshot!(doc);
    })
}
