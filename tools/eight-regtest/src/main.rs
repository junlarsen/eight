//! Eight Regtest, a regression testing tool for the Eight compiler.
//!
//! Regtest takes two inputs, a truth file read from stdin, and a test file read from the first
//! command line argument. It then compares the truth file with the snap file, and prints a diff
//! if they differ.
//!
//! The test file can be updated with the `-u` flag, which will update the snap file with the
//! contents of the truth file. This is useful for updating the snap file after verifying that the
//! new output is correct.

use clap::Parser;
use similar::{ChangeTag, TextDiff};
use std::fmt::Arguments;
use std::io::{Read, Write};
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};
use thiserror::Error;

#[derive(Parser)]
struct RegTestArgs {
    snap: String,

    #[clap(short, long)]
    update: bool,
}

#[derive(Debug, Error)]
#[error("regtest error: {0}")]
enum RegTestError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    #[error("snapshot path is not a file: {0}")]
    NotAFile(String),
}

/// Enum describing the different states the snapshot file can be in.
enum SnapshotState {
    /// The snapshot file does not exist, and will be created this run.
    ///
    /// The creation of the file will happen regardless of whether `-u` is provided to the
    /// command line. This is for convenience, as you'll likely want to generate the file if it
    /// doesn't exist.
    Fresh,
    /// The file matches the truth file
    Content(String),
}

fn get_snapshot_state(snapshot_path: &str) -> Result<SnapshotState, RegTestError> {
    if !std::fs::exists(snapshot_path)? {
        return Ok(SnapshotState::Fresh);
    }
    let metadata = std::fs::metadata(snapshot_path)?;
    if !metadata.is_file() {
        return Err(RegTestError::NotAFile(snapshot_path.to_string()));
    }
    let mut snapshot = String::new();
    std::fs::File::open(snapshot_path)?.read_to_string(&mut snapshot)?;
    Ok(SnapshotState::Content(snapshot))
}

fn main() -> anyhow::Result<()> {
    let args = RegTestArgs::parse();
    let mut writer = StandardStream::stdout(ColorChoice::Auto);

    let stdin = std::io::stdin();
    let mut truth = String::new();
    stdin.lock().read_to_string(&mut truth)?;

    let snapshot_state = get_snapshot_state(&args.snap)?;
    let snapshot = match &snapshot_state {
        SnapshotState::Fresh => "",
        SnapshotState::Content(snapshot) => snapshot,
    };

    // Compare and print the diffs
    let diff = TextDiff::from_lines(snapshot, truth.as_str());
    let mut changed = false;
    for change in diff.iter_all_changes() {
        // To avoid bleeding the color onto the next line, we write the newline after the change
        // and reset have been applied. Not doing this bleeds the diff colors out into the `lit`
        // output.
        let c = change.to_string().replace('\n', "");
        match change.tag() {
            ChangeTag::Equal => {
                writer.write_fmt(format_args!(" {}", c))?;
            }
            ChangeTag::Delete => {
                changed = true;
                write_colored(
                    &mut writer,
                    ColorSpec::new().set_fg(Some(Color::Red)),
                    format_args!("-{}", c),
                )?;
            }
            ChangeTag::Insert => {
                changed = true;
                write_colored(
                    &mut writer,
                    ColorSpec::new().set_fg(Some(Color::Green)),
                    format_args!("+{}", c),
                )?;
            }
        };
        writer.write_all(b"\n")?;
    }
    // If the snapshot file is fresh, we create it regardless.
    if args.update || matches!(snapshot_state, SnapshotState::Fresh) {
        std::fs::write(args.snap, truth)?;
    }
    std::process::exit(changed as i32);
}

fn write_colored(
    buffer: &mut impl WriteColor,
    color: &ColorSpec,
    args: Arguments<'_>,
) -> std::io::Result<()> {
    buffer.set_color(color)?;
    buffer.write_fmt(args)?;
    buffer.reset()?;
    Ok(())
}
