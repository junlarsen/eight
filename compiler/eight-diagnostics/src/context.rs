use crate::ice;
use miette::{Diagnostic, NamedSource, Report};
use std::borrow::Cow;
use std::cmp::min;
use std::path::PathBuf;
use std::sync::Mutex;

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
pub struct DiagnosticContext<'src> {
    diagnostics: Mutex<Vec<Report>>,
    src: &'src DiagnosticSource,
}

impl<'src> DiagnosticContext<'src> {
    /// Create a new diagnostic context.
    ///
    /// The `max_diagnostic_count` parameter specifies the maximum number of diagnostics that can
    /// be collected.
    pub fn new(src: &'src DiagnosticSource, max_diagnostic_count: usize) -> Self {
        Self {
            diagnostics: Mutex::new(Vec::with_capacity(min(max_diagnostic_count, 16))),
            src,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"))
            .is_empty()
    }

    /// Emit a unrecoverable, non-fatal diagnostic.
    pub fn emit_diagnostic(&self, diagnostic: impl Diagnostic + Sync + Send + 'static) {
        let mut diagnostics = self
            .diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"));
        diagnostics.push(Report::from(diagnostic));
    }

    /// Emit a fatal diagnostic, which will cause the compiler to exit immediately.
    pub fn emit_fatal_diagnostic(&self, diagnostic: impl Diagnostic + Sync + Send + 'static) -> ! {
        self.emit_diagnostic(diagnostic);
        self.report();
        std::process::exit(1);
    }

    /// Report all the collected diagnostics to stderr.
    pub fn report(&self) {
        let mut diagnostics = self
            .diagnostics
            .lock()
            .unwrap_or_else(|_| ice!("failed to acquire diagnostics lock"));

        for report in diagnostics.drain(..) {
            let (source_name, source) = match &self.src {
                DiagnosticSource::File(path, source) => (path.to_string_lossy(), source),
                DiagnosticSource::Stdin(source) => (Cow::Borrowed("stdin"), source),
            };
            let report = report.with_source_code(NamedSource::new(source_name, source.to_owned()));
            eprint!("Error: {:?}", report);
        }
    }
}
