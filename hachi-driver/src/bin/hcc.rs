use clap::Parser;
use hachi_parse::{Lexer, TranslationUnit};

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    input: String,

    #[arg(long, default_value = "false")]
    emit_ast: bool,
}

fn compile(input: &str) -> miette::Result<Box<TranslationUnit>> {
    let mut lexer = Lexer::new(input);
    let mut parser = hachi_parse::Parser::new(&mut lexer);
    let tu = parser.parse()?;
    Ok(tu)
}

fn main() -> miette::Result<()> {
    let args = AppArgs::parse();
    let source = std::fs::read_to_string(args.input.clone()).expect("Failed to read input file");
    let source_code = source.clone();

    let translation_unit = compile(&source).map_err(|e| e.with_source_code(source_code))?;

    if args.emit_ast {
        let syntax = ron::ser::to_string_pretty(&translation_unit, Default::default())
            .expect("failed to serialize ast to ron");
        println!("{}", syntax);
    }

    Ok(())
}
