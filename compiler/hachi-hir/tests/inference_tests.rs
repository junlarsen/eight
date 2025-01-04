mod common;

macro_rules! inference_test {
    ($src:expr) => {{
        use hachi_hir::passes::HirModuleDebugPass;
        let path = format!("{}/tests/{}", env!("CARGO_MANIFEST_DIR"), $src);
        let src = std::fs::read_to_string(path).unwrap();
        let module = assert_hir_module_infers!(&src);
        let doc = HirModuleDebugPass::format_hir_module_to_string(&module);
        insta::assert_snapshot!(doc);
    }};
}

#[test]
fn test_uninitialized_inference() {
    inference_test!("data/inference/uninitialized_inference.test");
}

#[test]
fn test_local_resolution() {
    inference_test!("data/inference/local_resolution.test");
}

#[test]
fn test_chaining_infers_unit() {
    inference_test!("data/inference/chaining_infers_unit.test");
}

#[test]
fn test_offset_index_yields_inner() {
    inference_test!("data/inference/offset_index_yields_inner.test");
}

#[test]
fn test_constant_record_access() {
    inference_test!("data/inference/constant_record_access.test");
}

#[test]
fn test_function_calls() {
    inference_test!("data/inference/function_calls.test");
}

#[test]
fn test_construction() {
    inference_test!(
        "data/inference/construction.te\
    st"
    );
}

#[test]
fn test_pointer_deref() {
    inference_test!("data/inference/pointer_deref.test");
}
