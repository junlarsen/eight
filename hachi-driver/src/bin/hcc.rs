use clap::Parser;
use hachi_parse::Lexer;
use miette::{Context, IntoDiagnostic};
use ron::ser::PrettyConfig;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    input: String,

    #[arg(long, default_value = "false")]
    emit_ast: bool,
}

fn main() -> miette::Result<()> {
    let args = AppArgs::parse();
    let source = std::fs::read_to_string(args.input).expect("Failed to read input file");

    let mut parser = hachi_parse::Parser::new(Lexer::new(&source));
    let tu = parser
        .parse()
        .into_diagnostic()
        .wrap_err("Failed to parse input file")?;

    if args.emit_ast {
        let tree =
            ron::ser::to_string_pretty(&tu, PrettyConfig::new()).expect("failed to serialize ast");
        println!("{}", tree);
    };

    Ok(())
}
