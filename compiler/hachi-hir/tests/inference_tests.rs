mod common;

macro_rules! inference_test {
    ($name:ident, $src:expr) => {
        #[test]
        fn $name() {
            use hachi_hir::format::HirModuleFormatter;

            let path = format!("{}/tests/{}", env!("CARGO_MANIFEST_DIR"), $src);
            let src = std::fs::read_to_string(path).unwrap();
            let module = assert_hir_module_infers!(&src);
            let doc = HirModuleFormatter::format_hir_module_to_string(&module);
            insta::assert_snapshot!(doc);
        }
    };
}

inference_test!(
    test_inference_uninitialized_inference,
    "data/inference/uninitialized_inference.test"
);
inference_test!(
    test_inference_local_resolution,
    "data/inference/local_resolution.test"
);
inference_test!(
    test_inference_chaining_infers_unit,
    "data/inference/chaining_infers_unit.test"
);
