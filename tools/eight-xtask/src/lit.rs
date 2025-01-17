use clap::Parser;
use std::process::Command;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
pub struct LitArgs {}

/// Run the LLVM Integrated Tester through the command line.
pub fn execute_lit_command(_: LitArgs) {
    let cwd = env!("CARGO_WORKSPACE_DIR");
    let mut cmd = Command::new("poetry");
    cmd.current_dir(cwd);
    cmd.arg("run");
    cmd.arg("lit");
    cmd.arg("tests");
    cmd.arg("-v");
    let mut child = cmd.spawn().expect("failed to spawn lit");
    child.wait().expect("lit failed");
}
