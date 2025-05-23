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

fn simplify_module(module: &modcxx::ast::Module) -> Result<modcxx::ast::Module> {
    let mut new = module
        .clone()
        .inline_procedures()?
        // .inline_functions()?
        .kinetic_to_sparse()?
        .simplify()?
        // .collect_ode_systems()?
        .simplify()?
        .solve_odes()?
        .simplify()?;
    loop {
        let nxt = new
            .clone()
            .assigned_to_local()?
            .eliminate_dead_blocks()?
            .splat_blocks()?
            .eliminate_dead_globals()?
            .eliminate_dead_calls()?
            .eliminate_dead_local_assignments()?
            .eliminate_dead_state()?
            .simplify()?;
        if nxt == new {
            break;
        }
        new = nxt;
    }
    // final clean up
    let new = new.eliminate_dead_locals()?;
    Ok(new)
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Arborize { from, to } => {
            let raw = read_to_string(&from).map_err(|_| {
                ModcxxError::InternalError(format!("Could not open input file {}", &from))
            })?;
            let src = modcxx::par::parse(&raw)?;
            let ast = modcxx::ast::Module::new(&src)?;
            let new = simplify_module(&ast)?;
            let arb = arborize(&new)?;
            let out = to_nmodl(&arb)?;
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
            let ast = modcxx::ast::Module::new(&src)?;
            let new = simplify_module(&ast)?;
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
