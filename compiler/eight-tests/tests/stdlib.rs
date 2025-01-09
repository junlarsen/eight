use eight_driver::pipeline::{Pipeline, PipelineOptions};
use insta_cmd::get_cargo_bin;
use std::path::Path;
use std::process::Command;

#[test]
fn test_evaluate_stdlib() {
    let path = Path::join(env!("CARGO_MANIFEST_DIR").as_ref(), "../../stdlib");
    let files = std::fs::read_dir(path)
        .expect("failed to read stdlib directory")
        .filter_map(|f| f.ok())
        .filter(|f| {
            std::fs::metadata(f.path())
                .expect("failed to stat file")
                .is_file()
        });
    let mut buf = String::new();
    for file in files {
        let path = file.path();
        let content = std::fs::read_to_string(path).expect("failed to read file");
        buf.push_str(&content);
        buf.push('\n');
    }

    let mut cmd = Command::new(get_cargo_bin("eightc"));
    insta_cmd::assert_cmd_snapshot!(cmd.arg("-").arg("--emit-hir").pass_stdin(buf));
}
