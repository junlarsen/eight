use clap::Parser;
use eight_driver::pipeline::{
    execute_compilation_pipeline, PipelineOptions,
};
use miette::NamedSource;
use std::io::BufRead;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    /// The input source. If this is `-`, the input is read from stdin.
    input: String,

    /// Should the plain AST be emitted?
    #[arg(long, default_value = "false")]
    emit_ast: bool,

    /// Should the fully-typed, lowered HIR be emitted?
    #[arg(long, default_value = "false")]
    emit_hir: bool,

    /// Emission queries to specify which nodes should be emitted.
    #[arg(long, default_value = "")]
    emit_query: Vec<String>,
}

impl From<AppArgs> for PipelineOptions {
    fn from(args: AppArgs) -> Self {
        Self {
            emit_ast: args.emit_ast,
            emit_hir: args.emit_hir,
            queries: vec![]
        }
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
    let options = PipelineOptions::from(args);

    let result = || -> miette::Result<()> {
        execute_compilation_pipeline(options, &source)?;
        Ok(())
    }();
    result.map_err(|e| e.with_source_code(source_code))?;
    Ok(())
}
