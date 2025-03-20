pub mod args;
pub mod error_reporting;
pub mod fresh_var;
pub mod lexer;
pub mod parser;
pub mod pretty;
pub mod ren;
pub mod rep;
pub mod semantics;
pub mod syntax;
pub mod type_checker;
pub mod type_context;
pub mod util;

#[cfg(test)]
mod tests;

use std::process::exit;

use clap::Parser;
use syntax::SExpr;

use crate::{
    args::Args,
    error_reporting::{report_error, IErr},
    lexer::Token,
    semantics::eval,
    syntax::{Eff, Type},
    util::{
        lexer_offside::{self, Braced},
        pretty::pretty_def,
    },
};

fn main() {
    let args = Args::parse();
    let src_path = args.src_path.to_string_lossy();
    if let Err(e) = run(&args) {
        let src = std::fs::read_to_string(&*src_path).unwrap();
        report_error(&src_path, &src, e);
        exit(1)
    }
}

pub fn run(args: &Args) -> Result<(), IErr> {
    let src = std::fs::read_to_string(&args.src_path).unwrap();
    if args.verbose {
        println!("===== SRC =====");
        println!("{src}");
        println!();
    }
    let (e, _t, _p) = typecheck(&src, args.verbose)?;

    println!("===== EVALUATION =====");
    println!("Program stdout:");
    let v = eval(&e).map_err(IErr::Eval)?;
    println!(
        "Program terminated successfully with value `{}`.",
        pretty_def(&v)
    );
    Ok(())
}

pub fn typecheck(src: &str, verbose: bool) -> Result<(SExpr, Type, Eff), IErr> {
    // println!("===== TOKENS =====");
    let toks = lexer::lex(&src).map_err(IErr::Lexer)?;
    // for (i, t) in toks.toks.iter().enumerate() {
    //     println!("{i}:\t{t:?}");
    // }
    // println!();

    let mut toks = lexer_offside::process_indent(toks, |_| false, |_| false);
    toks.toks = toks
        .toks
        .into_iter()
        .filter(|t| t.val != Braced::Token(Token::NewLine))
        .collect::<Vec<_>>();
    if verbose {
        println!("===== TOKENS =====");
        for (i, t) in toks.toks.iter().enumerate() {
            println!("{i}:\t{t:?}");
        }
        println!();
    }

    let mut e = parser::parse(&toks).map_err(IErr::Parser)?;
    if verbose {
        println!("===== AST =====");
        println!("{e:#?}");
        println!();
    }

    if verbose {
        println!("===== PRETTY =====");
        println!("{}", pretty_def(&e));
        println!();
    }

    println!("===== TYPECHECKER =====");
    let (t, p) = type_checker::infer_type(&mut e).map_err(IErr::Typing)?;
    println!("Type:    {}", pretty_def(&t));
    println!("Effect:  {}", pretty_def(&p));
    println!();

    Ok((e, t.val, p))
}
