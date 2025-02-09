//! Eight Regtest, a regression testing tool for the Eight compiler.
//!
//! Regtest takes two inputs, a truth file read from stdin, and a test file read from the first
//! command line argument. It then compares the truth file with the snap file, and prints a diff
//! if they differ.

use owo_colors::OwoColorize;
use similar::TextDiff;
use std::io::Read;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Debug, Error)]
#[error("regtest error: {0}")]
pub enum RegTestError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("snapshot path is not a file: {0}")]
    InvalidPath(PathBuf),
    #[error("both fresh and updated snapshot files exist: {0} and {1}. delete one of them.")]
    Conflict(PathBuf, PathBuf),
}

/// Enum describing the different states the snapshot file can be in.
#[derive(Debug)]
pub enum SnapshotState {
    /// The snapshot file does not exist, and will be created this run.
    ///
    /// The creation of the file will happen regardless of whether `-u` is provided to the
    /// command line. This is for convenience, as you'll likely want to generate the file if it
    /// doesn't exist.
    Fresh,
    /// The file has seen some changes (i.e, has .tmpsnap extension)
    Unverified(String),
    /// The file has not seen any changes and was previously accepted. (i.e, has only .snap
    /// extension)
    Verified(String),
    /// The file regressed due to some recent changes. It means that both .regsnap and .tmpsnap
    /// exist.
    ///
    /// The tuple is (regsnap, tmpsnap) file contents respectively.
    PreviouslyRegressed(String, String),
}

pub fn get_verified_snapshot_path<P: AsRef<Path>>(path: P) -> PathBuf {
    let mut buf = path.as_ref().as_os_str().to_owned();
    buf.push(".snap");
    PathBuf::from(buf)
}

pub fn get_updated_snapshot_path<P: AsRef<Path>>(path: P) -> PathBuf {
    let mut buf = path.as_ref().as_os_str().to_owned();
    buf.push(".tmpsnap");
    PathBuf::from(buf)
}

pub fn get_regressed_snapshot_path<P: AsRef<Path>>(path: P) -> PathBuf {
    let mut buf = path.as_ref().as_os_str().to_owned();
    buf.push(".regsnap");
    PathBuf::from(buf)
}

/// Get the snapshot state for the given snapshot file.
pub fn get_snapshot_state<P: AsRef<Path>>(path: P) -> Result<SnapshotState, RegTestError> {
    let updated_snapshot_candidate_path = get_updated_snapshot_path(path.as_ref());
    let updated_exists = std::fs::exists(&updated_snapshot_candidate_path)?;
    let verified_snapshot_candidate_path = get_verified_snapshot_path(path.as_ref());
    let verified_exists = std::fs::exists(&verified_snapshot_candidate_path)?;

    match (updated_exists, verified_exists) {
        // If both files exist, we have a conflict and should error out.
        (true, true) => Err(RegTestError::Conflict(
            updated_snapshot_candidate_path,
            verified_snapshot_candidate_path,
        )),
        // An updated snapshot file exists, but the fresh snapshot file does not. This means that
        // the snapshot should be verified by the user.
        (true, false) => {
            let metadata = std::fs::metadata(&updated_snapshot_candidate_path)?;
            // If the inode at the path is not a file, then something is obstructing the inode path
            // from being used properly, so this should be an error.
            if !metadata.is_file() {
                return Err(RegTestError::InvalidPath(updated_snapshot_candidate_path));
            }
            let mut snapshot = String::new();
            std::fs::File::open(&updated_snapshot_candidate_path)?.read_to_string(&mut snapshot)?;
            // If the file was a regression, we also read and return the regressed snapshot.
            let regressed_snapshot_path = get_regressed_snapshot_path(path.as_ref());
            if std::fs::exists(&regressed_snapshot_path)? {
                let mut regressed_snapshot = String::new();
                std::fs::File::open(&regressed_snapshot_path)?
                    .read_to_string(&mut regressed_snapshot)?;
                return Ok(SnapshotState::PreviouslyRegressed(
                    regressed_snapshot,
                    snapshot,
                ));
            }
            Ok(SnapshotState::Unverified(snapshot))
        }
        // A verified snapshot file exists.
        (false, true) => {
            let metadata = std::fs::metadata(&verified_snapshot_candidate_path)?;
            // If the inode at the path is not a file, then something is obstructing the inode path from
            // being used properly, so this should be an error.
            if !metadata.is_file() {
                return Err(RegTestError::InvalidPath(verified_snapshot_candidate_path));
            }
            let mut snapshot = String::new();
            std::fs::File::open(&verified_snapshot_candidate_path)?
                .read_to_string(&mut snapshot)?;
            Ok(SnapshotState::Verified(snapshot))
        }
        // Neither file exists, so we should create a fresh snapshot file.
        (false, false) => Ok(SnapshotState::Fresh),
    }
}

/// Get the annotated diff between the truth and snapshot.
///
/// Returns a tuple of (changed, diff) where changed is true if the snapshot file has changed.
pub fn get_annotated_diff(truth: &str, snapshot: &str) -> (bool, String) {
    let diff = TextDiff::from_lines(snapshot, truth);
    let mut buf = String::new();
    let mut changed = false;
    for change in diff.iter_all_changes() {
        // To avoid bleeding the color onto the next line, we write the newline after the change
        // and reset have been applied. Not doing this bleeds the diff colors out into the `lit`
        // output.
        let c = change.to_string().replace('\n', "");
        match change.tag() {
            similar::ChangeTag::Equal => {
                buf.push_str(&c);
            }
            similar::ChangeTag::Delete => {
                changed = true;
                buf.push_str(&format!("-{}", c.red()));
            }
            similar::ChangeTag::Insert => {
                changed = true;
                buf.push_str(&format!("+{}", c.green()));
            }
        };
        buf.push('\n');
    }

    (changed, buf)
}

pub fn get_unverified_snapshots<P: AsRef<Path>>(path: P) -> Result<Vec<PathBuf>, RegTestError> {
    let mut buf = Vec::new();
    fn is_unverified_snapshot(path: &Path) -> bool {
        path.is_file() && path.extension().is_some_and(|ext| ext == "tmpsnap")
    }
    /// Recursively visit the given path, and collect all unverified snapshots.
    fn visit(path: &Path, buf: &mut Vec<PathBuf>) -> Result<(), RegTestError> {
        let metadata = std::fs::metadata(path)?;
        if metadata.is_dir() {
            for entry in std::fs::read_dir(path)? {
                let path = entry?.path();
                if path.is_dir() {
                    visit(&path, buf)?;
                }
                // If it's a file and it has the .tmpsnap extension, we count it as an unverified
                // snapshot.
                if is_unverified_snapshot(&path) {
                    buf.push(path);
                }
            }
        }
        // Otherwise, if it's a file
        if is_unverified_snapshot(path) {
            buf.push(path.to_owned());
        }
        Ok(())
    }
    visit(path.as_ref(), &mut buf)?;
    Ok(buf)
}
