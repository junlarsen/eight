use clap::Parser;
use hachi_hir::HirModule;
use hachi_syntax::{Lexer, TranslationUnit};
use hachi_syntax_lower::SyntaxLoweringPass;
use miette::NamedSource;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    input: String,

    #[arg(long, default_value = "false")]
    emit_ast: bool,
}

fn compile(input: &str) -> miette::Result<(TranslationUnit, HirModule)> {
    let mut lexer = Lexer::new(input);
    let mut parser = hachi_syntax::Parser::new(&mut lexer);
    let mut lowering_pass = SyntaxLoweringPass::new();
    let tu = parser.parse()?;
    let module = lowering_pass.visit_translation_unit(&tu)?;
    Ok((tu, module))
}

fn main() -> miette::Result<()> {
    let args = AppArgs::parse();
    let source = std::fs::read_to_string(args.input.clone()).expect("Failed to read input file");
    let source_code = NamedSource::new(args.input, source.clone());

    let (tu, module) = compile(&source).map_err(|e| e.with_source_code(source_code))?;

    if args.emit_ast {
        let syntax = ron::ser::to_string_pretty(&tu, Default::default())
            .expect("failed to serialize ast to ron");
        println!("{}", syntax);
    }

    Ok(())
}
