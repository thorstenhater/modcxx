use std::fs::{self, read_to_string};

use modcxx::{
    self,
    arb::arborize,
    cxx::to_cxx,
    err::{ModcxxError, Result},
    nmd::to_nmodl,
    opt::Simplify,
};

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[clap(name = "nmlcc")]
#[clap(version = "0.1.0-dev", author = "t.hater@fz-juelich.de")]
struct Cli {
    #[clap(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    Arborize { from: String, to: Option<String> },
    CodeGen { from: String, to: Option<String> },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Arborize { from, to } => {
            let raw = read_to_string(&from).map_err(|_| {
                ModcxxError::InternalError(format!("Could not open input file {}", &from))
            })?;
            let src = modcxx::par::parse(&raw)?;
            let mut new = modcxx::ast::Module::new(&src)?;
            loop {
                let nxt = new
                    .clone()
                    .inline_procedures()?
                    // .inline_functions()?
                    .kinetic_to_sparse()?
                    .assigned_to_local()?
                    .eliminate_dead_blocks()?
                    .splat_blocks()?
                    .eliminate_dead_statements()?
                    .eliminate_dead_globals()?
                    .eliminate_dead_locals()?
                    .simplify()?;
                if nxt == new {
                    break;
                }
                new = nxt;
            }
            let new = arborize(&new)?;
            let out = to_nmodl(&new)?;
            if let Some(to) = to {
                fs::write(to, out).map_err(|_| {
                    ModcxxError::InternalError("Couldn't open output file".to_string())
                })?;
            } else {
                println!("{}", out);
            }
        }
        Cmd::CodeGen { from, to } => {
            let raw = read_to_string(&from).map_err(|_| {
                ModcxxError::InternalError(format!("Could not open input file {}", &from))
            })?;
            let src = modcxx::par::parse(&raw)?;
            let mut new = modcxx::ast::Module::new(&src)?;
            loop {
                let nxt = new
                    .clone()
                    .eliminate_dead_blocks()?
                    .inline_procedures()?
                    // .inline_functions()?
                    .eliminate_dead_blocks()?
                    .splat_blocks()?
                    .eliminate_dead_blocks()?
                    .eliminate_dead_statements()?
                    .eliminate_dead_globals()?
                    .eliminate_dead_locals()?
                    .assigned_to_local()?;
                if nxt == new {
                    break;
                }
                new = nxt;
            }
            let new = arborize(&new)?;
            let out = to_cxx(&new)?;
            if let Some(to) = to {
                fs::write(to, out).map_err(|_| {
                    ModcxxError::InternalError("Couldn't open output file".to_string())
                })?;
            } else {
                println!("{}", out);
            }
        }
    }
    Ok(())
}
