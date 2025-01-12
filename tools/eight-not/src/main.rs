//! A port of LLVM `eight-not` written for the Eight compiler in Rust.
//!
//! Because we're using LLVM out-of-tree, we cannot just use `eight-not` like the Lit tests in the LLVM
//! test suite.
//!
//! https://github.com/llvm/llvm-project/blob/main/llvm/utils/not/not.cpp
//!
//! This implementation is eight-not fully compatible with LLVM `eight-not`, as we don't support the `--crash`
//! flag.

use std::collections::VecDeque;
use std::process::Command;

fn main() {
    // Collect the program arguments, and discard the program name.
    let mut args = std::env::args().collect::<VecDeque<_>>();
    args.pop_front();

    // We didn't expect a crash, and nothing else was specified.
    let Some(command) = args.pop_front() else {
        std::process::exit(1);
    };

    // Build the command, and forward all arguments to it.
    let mut command = Command::new(command);
    while let Some(arg) = args.pop_front() {
        command.arg(arg);
    }
    let mut handle = command.spawn().expect("failed to launch child process");
    let status = handle.wait().expect("failed to wait on child process");

    // Invert the exit code of the child process.
    if status.success() {
        std::process::exit(1);
    }
    std::process::exit(0);
}
