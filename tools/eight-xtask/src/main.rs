mod lit;

use clap::{Parser, Subcommand};

#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Lit(lit::LitArgs),
}

fn main() {
    let args = Args::parse();
    match args.command {
        Commands::Lit(lit_args) => lit::execute_lit_command(lit_args),
    }
}
