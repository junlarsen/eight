use clap::Parser;
use eight_driver::pipeline::{
    execute_compilation_pipeline, PipelineError, PipelineOptions, StopTokenStep,
};
use eight_driver::query::{EmitQuery, QueryError};
use miette::NamedSource;
use std::io::BufRead;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
#[clap()]
struct AppArgs {
    /// The input source. If this is `-`, the input is read from stdin.
    input: String,

    /// Should the plain AST be emitted?
    #[arg(long, default_value = "false")]
    emit_ast: bool,

    /// Should the fully-typed, lowered HIR be emitted?
    #[arg(long, default_value = "false")]
    emit_hir: bool,

    /// Should the MIR be emitted?
    #[arg(long, default_value = "false")]
    emit_mir: bool,

    /// Emission queries to specify which nodes should be emitted.
    #[arg(long)]
    emit_query: Option<Vec<String>>,

    /// Stop the compiler after the type checker.
    #[arg(long, default_value = "false", group = "stop-token")]
    syntax_only: bool,

    /// Stop the compiler after MIR lowering.
    #[arg(long, default_value = "false", group = "stop-token")]
    mir_only: bool,
}

// NOTE: We don't care to use From here, because the PipelineOptions should be completely
// independent of AppArgs. For all the PipelineOptions knows, the AppArgs don't even exist.
impl TryInto<PipelineOptions> for AppArgs {
    type Error = QueryError;

    fn try_into(self) -> Result<PipelineOptions, Self::Error> {
        let queries = self
            .emit_query
            .map(|q| EmitQuery::from_queries(&q.iter().map(|s| s.as_str()).collect::<Vec<_>>()))
            .transpose()?
            .unwrap_or_default();
        let token = match (self.syntax_only, self.mir_only) {
            (true, _) => Some(StopTokenStep::Frontend),
            (_, true) => Some(StopTokenStep::Middle),
            _ => None,
        };
        Ok(PipelineOptions {
            emit_ast: self.emit_ast,
            emit_hir: self.emit_hir,
            emit_mir: self.emit_mir,
            stop_token: token,
            queries,
        })
    }
}

fn main() -> miette::Result<()> {
    let args = AppArgs::parse();

    let source = match args.input.as_str() {
        "-" => std::io::stdin()
            .lock()
            .lines()
            .collect::<Result<String, _>>()
            .expect("failed to read from stdin"),
        path => std::fs::read_to_string(path).expect("Failed to read input file"),
    };
    let source_code = NamedSource::new(&args.input, source.clone());

    let result = || -> miette::Result<()> {
        let options = args.try_into()?;
        match execute_compilation_pipeline(options, &source) {
            Ok(_) => Ok(()),
            Err(PipelineError::StopToken(msg)) => {
                eprintln!("eightc: early termination due to: {}", msg);
                std::process::exit(0);
            }
            Err(e) => Err(e),
        }?;
        Ok(())
    }();
    result.map_err(|e| e.with_source_code(source_code))?;
    Ok(())
}
