use clap::Parser;

#[derive(clap::Parser)]
#[command(version, about, long_about = None)]
struct AppArgs {
    input: String,
}

fn main() {
    let args = AppArgs::parse();
    let source = std::fs::read_to_string(args.input).expect("Failed to read input file");
    println!("{}", source);
}
