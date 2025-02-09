use clap::{Parser, Subcommand};
use eight_regtest::{
    get_annotated_diff, get_base_path, get_regressed_snapshot_path, get_snapshot_state,
    get_unverified_snapshots, get_updated_snapshot_path, get_verified_snapshot_path, SnapshotState,
};
use inquire::Select;
use owo_colors::OwoColorize;
use std::io::Read;

#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

/// A subcommand selected for the regtest binary.
#[derive(Subcommand)]
enum Command {
    /// Test stdin against the provided snapshot file.
    Test(CommandTestArgs),
    /// Interactively update each snapshot file in the provided directory, recursively.
    Verify(CommandVerifyArgs),
}

#[derive(Parser)]
struct CommandTestArgs {
    snapshot: String,
}

#[derive(Parser)]
struct CommandVerifyArgs {
    directory: String,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    match args.command {
        Command::Test(args) => test(args),
        Command::Verify(args) => verify(args),
    }
}

/// Compare the file on stdin against the snapshot file.
///
/// If the snapshot file does not exist, it will be created, and marked as fresh. The program will
/// exit with a non-zero exit code and print a diff.
///
/// It is now up to the user to verify the snapshot using `regtest verify`.
fn test(args: CommandTestArgs) -> anyhow::Result<()> {
    let snapshot_state = get_snapshot_state(&args.snapshot)?;
    let snapshot = match &snapshot_state {
        SnapshotState::Fresh | SnapshotState::Unverified(_) => "",
        SnapshotState::Verified(snapshot) => snapshot,
        SnapshotState::PreviouslyRegressed(regression, _) => regression,
    };
    let mut stdin = String::new();
    std::io::stdin().lock().read_to_string(&mut stdin)?;
    let (changed, diff) = get_annotated_diff(&stdin, snapshot);

    // If there were no changes, and the snapshot file was previously verified, we can exit early.
    if !changed && matches!(snapshot_state, SnapshotState::Verified(_)) {
        std::process::exit(0);
    }

    // Otherwise, we let the user know that the snapshot file has changed.
    match snapshot_state {
        SnapshotState::Fresh => println!("{}\n", "A new snapshot has been created".cyan()),
        SnapshotState::Unverified(_) => println!(
            "{}\n",
            "The snapshot has not been reviewed since last run".cyan()
        ),
        // The output has diverged, so we mark the file as regressed in addition to producing the
        // new tmpsnap file.
        SnapshotState::Verified(_) | SnapshotState::PreviouslyRegressed(_, _) => {
            println!("{}\n", "The snapshot has regressed".cyan());
        }
    }

    // This means the regression is fresh to this `regtest test` run, so we can write the regressed
    // snapshot into the .regsnap file.
    if matches!(snapshot_state, SnapshotState::Verified(_)) {
        let verified_snapshot_path = get_verified_snapshot_path(&args.snapshot);
        let regressed_snapshot_path = get_regressed_snapshot_path(&args.snapshot);
        std::fs::rename(&verified_snapshot_path, &regressed_snapshot_path)?;
    }

    println!("{}", diff);
    // Write back the updated snapshot into the .tmpsnap file
    let updated_snapshot_path = get_updated_snapshot_path(&args.snapshot);
    std::fs::write(&updated_snapshot_path, &stdin)?;
    println!(
        "{} {}\n",
        "The snapshot has been written to".cyan(),
        updated_snapshot_path.display()
    );
    std::process::exit(1);
}

/// Interactively verify each snapshot file in the provided directory.
///
/// This gives the user the choice between ACCEPT / IGNORE / REJECT each snapshot file. Based on the
/// selection, the behavior is as follows:
///
/// 1. ACCEPT: The snapshot file is marked accepted
/// 2. IGNORE: The snapshot file is left as-is with no modifications to its state
/// 3. REJECT: The snapshot file is deleted. Consequently, future `regtest test` runs will end up
///    creating the snapshot file again.
fn verify(args: CommandVerifyArgs) -> anyhow::Result<()> {
    let options = ["ACCEPT", "IGNORE", "REJECT"];
    let unverified_snapshots = get_unverified_snapshots(&args.directory)?;
    for path in unverified_snapshots {
        clearscreen::clear()?;
        let base_path = get_base_path(&path);
        let state = get_snapshot_state(&base_path)?;
        let (previous, current) = match &state {
            SnapshotState::Verified(s) | SnapshotState::Unverified(s) => ("", s.as_str()),
            SnapshotState::PreviouslyRegressed(r, s) => (r.as_str(), s.as_str()),
            SnapshotState::Fresh => unreachable!(
                "should not be possible to have just-verified snapshot in verification step"
            ),
        };

        let (_, diff) = get_annotated_diff(current, previous);
        println!(
            "{} {}",
            "Displaying diff for snapshot file".cyan(),
            path.display()
        );
        println!("{}", diff);
        let answer = Select::new("Select action for snapshot", options.to_vec()).prompt()?;
        match answer {
            "ACCEPT" => {
                // Move the unverified snapshot to the verified snapshot path, and potentially
                // delete a regressed snapshot if it exists.
                std::fs::rename(&path, get_verified_snapshot_path(&base_path))?;
                if matches!(state, SnapshotState::PreviouslyRegressed(_, _)) {
                    let regressed_snapshot_path = get_regressed_snapshot_path(&base_path);
                    std::fs::remove_file(&regressed_snapshot_path)?;
                }
            }
            "REJECT" => {
                std::fs::remove_file(&path)?;
                // If we rejected a regression, we move the regressed snapshot back to .snap
                if matches!(state, SnapshotState::PreviouslyRegressed(_, _)) {
                    let regressed_snapshot_path = get_regressed_snapshot_path(&base_path);
                    std::fs::rename(
                        &regressed_snapshot_path,
                        get_verified_snapshot_path(&base_path),
                    )?;
                }
            }
            // Do nothing
            "IGNORE" => {}
            _ => unreachable!(),
        }
    }
    Ok(())
}
