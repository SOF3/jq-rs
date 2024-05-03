use clap::Parser;

#[derive(Parser)]
struct Args {
    #[arg(short)]
    slurp: bool,
    /// Concatenate multiple inputs together directly, instead of treating them as separate inputs.
    #[arg(long)]
    concat: bool,
    program: String,
    inputs: Vec<String>,
}

fn main() -> jq_rs::Result<()> {
    let args = Args::parse();

    let mut program = jq_rs::compile(&args.program)?;

    if args.slurp {
        match program.run_slurp(
            args.inputs
                .iter()
                .map(String::as_str)
                .flat_map(|input| [input, if args.concat { "" } else { "\n" }]),
        ) {
            Ok(s) => print!("{}", s), // The output will include a trailing newline
            Err(e) => eprintln!("{}", e),
        }
    } else {
        match program.run(args.inputs.get(0).map(String::as_str).unwrap_or("")) {
            Ok(s) => print!("{}", s), // The output will include a trailing newline
            Err(e) => eprintln!("{}", e),
        }
    }

    Ok(())
}
