use clap::Parser;
use eight_driver::pipeline::{Pipeline, PipelineOptions};
use miette::NamedSource;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    input: String,
    #[arg(long, default_value = "false")]
    emit_ast: bool,
    #[arg(long, default_value = "false")]
    emit_hir: bool,
}

impl From<AppArgs> for PipelineOptions {
    fn from(args: AppArgs) -> Self {
        Self {
            emit_ast: args.emit_ast,
            emit_hir: args.emit_hir,
        }
    }
}

fn main() -> miette::Result<()> {
    let args = AppArgs::parse();
    let source = std::fs::read_to_string(args.input.clone()).expect("Failed to read input file");
    let source_code = NamedSource::new(&args.input, source.clone());

    let options = PipelineOptions::from(args);
    let pipeline = Pipeline::new(options);
    pipeline
        .run(source)
        .map_err(|e| e.with_source_code(source_code))?;
    Ok(())
}