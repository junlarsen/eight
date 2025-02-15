use crate::ice;
use miette::{Diagnostic, NamedSource, Report};
use std::borrow::Cow;
use std::cmp::min;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Mutex;
use thiserror::Error;

/// A token that indicates that an error occurred.
///
/// The diagnostic associated with this error has been collected.
#[derive(Error, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
#[error("error dispatched through diagnostic context")]
pub struct ErrorGuaranteed(pub(crate) ());

#[derive(Debug)]
pub enum DiagnosticSource {
    File(PathBuf, String),
    Stdin(String),
}

impl DiagnosticSource {
    pub fn source(&self) -> &str {
        match self {
            DiagnosticSource::File(_, source) => source,
            DiagnosticSource::Stdin(source) => source,
        }
    }
}

/// A context collector for compiler diagnostics.
///
/// This type holds diagnostics collected during the compilation process. It is used to allow
/// different parts of the compiler to report diagnostics consistently.
///
/// Diagnostics can either recoverable, unrecoverable (but still allow compilation to continue in
/// order to collect more diagnostics), or fatal (the compiler should exit immediately).
pub struct DiagnosticContext {
    diagnostics: Mutex<Vec<Report>>,
    errors: Mutex<Vec<ErrorGuaranteed>>,
    src: Rc<DiagnosticSource>,
}

impl DiagnosticContext {
    /// Create a new diagnostic context.
    ///
    /// The `max_diagnostic_count` parameter specifies the maximum number of diagnostics that can
    /// be collected.
    pub fn new(src: Rc<DiagnosticSource>, max_diagnostic_count: usize) -> Self {
        Self {
            src,
            errors: Mutex::new(Vec::new()),
            diagnostics: Mutex::new(Vec::with_capacity(min(max_diagnostic_count, 16))),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"))
            .is_empty()
    }

    pub fn emit(&self, diagnostic: impl Diagnostic + Sync + Send + 'static) -> ErrorGuaranteed {
        let mut diagnostics = self
            .diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"));
        diagnostics.push(Report::from(diagnostic));
        // At the moment we don't have warnings, so we always return an error here.
        let err = ErrorGuaranteed(());
        let mut errors = self
            .errors
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire error set lock"));
        errors.push(err);
        // Give the lock to get_emitted_error()
        drop(errors);
        self.get_emitted_error()
    }

    /// Get the last emitted ErrorGuaranteed reference.
    ///
    /// It being the last error holds no importance because ErrorGuaranteed is opaque, but it does
    /// ensure that an error was emitted before returning a reference to an ErrorGuaranteed.
    pub fn get_emitted_error(&self) -> ErrorGuaranteed {
        let errors = self
            .errors
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire error set locl"));
        let err = errors.last().unwrap_or_else(|| {
            ice!("attempted to get previously emitted error with zero recorded errors")
        });
        err.to_owned()
    }

    /// Report all the collected diagnostics to stderr.
    pub fn report(&self) {
        let mut diagnostics = self
            .diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"));

        for report in diagnostics.drain(..) {
            let (source_name, source) = match self.src.as_ref() {
                DiagnosticSource::File(path, source) => (path.to_string_lossy(), source),
                DiagnosticSource::Stdin(source) => (Cow::Borrowed("stdin"), source),
            };
            let report = report.with_source_code(NamedSource::new(source_name, source.to_owned()));
            eprint!("Error: {:?}", report);
        }
    }
}
