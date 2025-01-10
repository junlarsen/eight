//! End-to-end tests for the compiler with a variety of different inputs and compiler options.

macro_rules! compiler_test_suite {
    ($name:ident, $directory:expr, [$($arg:expr),*]) => {
        #[test]
        fn $name() {
            use std::process::Command;

            insta::with_settings!({
                description => format!("compiler test suite for {}", stringify!($name)),
                snapshot_path => concat!(env!("CARGO_MANIFEST_DIR"), "/tests/snapshots/", stringify!($name)),
            }, {
                insta::glob!(concat!($directory, "/**/*.test"), |path| {
                    let mut cmd = Command::new(insta_cmd::get_cargo_bin("eightc"));
                    $(cmd.arg($arg);)*
                    let relative = path.strip_prefix(env!("CARGO_MANIFEST_DIR"))
                        .expect("failed to build relative path from Cargo.toml");
                    insta_cmd::assert_cmd_snapshot!(cmd.arg(relative));
                });
            })
        }
    }
}

compiler_test_suite!(ui, "ui", []);
compiler_test_suite!(syntax, "syntax", ["--emit-ast"]);
compiler_test_suite!(syntax_lowering, "syntax-lowering", ["--emit-hir"]);
compiler_test_suite!(type_inference, "type-inference", ["--emit-hir"]);
