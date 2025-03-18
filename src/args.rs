use std::path::PathBuf;

use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Path to the source file to typecheck and run.
    #[arg(value_name = "FILE")]
    pub src_path: PathBuf,

    /// Print debug information for lexer, parser, etc.
    #[arg(short = 'v', long = "verbose")]
    pub verbose: bool,
}
