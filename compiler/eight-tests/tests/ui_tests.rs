//! Snapshot tests for the user interface reported by the compiler.
//!
//! These tests are performed by running the compiler for each of the files in the `ui` directory,
//! recursively.
//!
//! The goal is for each of the tests to fail, and for us to be able to view the output of the
//! compiler, ensuring that we're getting useful and precise error messages.

use insta_cmd::get_cargo_bin;
use std::process::Command;

#[test]
fn test_compiler_ui_tests() {
    insta::glob!("ui/**/*.test", |path| {
        let mut cmd = Command::new(get_cargo_bin("eightc"));
        let relative = path.strip_prefix(env!("CARGO_MANIFEST_DIR")).unwrap();
        insta_cmd::assert_cmd_snapshot!(cmd.arg(relative));
    });
}
