#![feature(
    iter_intersperse,
    exact_size_is_empty,
    assert_matches,
    let_chains,
    round_char_boundary,
    iter_chain
)]
#![allow(irrefutable_let_patterns)]

mod ast;
mod err;
mod kernel;
mod log;
mod parse;

use crate::ast::sugared;

use std::{path::PathBuf, time::Instant};

use anyhow::Context;
use ast::{desugared, Ident};
use codespan_reporting::files::SimpleFiles;
use yansi::Paint;

#[derive(Debug)]
struct Args {
    path: PathBuf,
}

impl Args {
    fn print_help() {
        print!(
            "kwed {}
https://github.com/jacobhenn/kwed
A minimal but powerful type-theoretic proof language.
            
USAGE:
    kwed <FILE_PATH>

",
            env!("CARGO_PKG_VERSION")
        );
    }

    fn from_env() -> anyhow::Result<Self> {
        use lexopt::prelude::*;

        let mut arg_parser = lexopt::Parser::from_env();

        let mut path = None;

        let arg = arg_parser.next()?;
        match arg {
            Some(Long("help")) => {
                Self::print_help();
                std::process::exit(0);
            }
            Some(Value(path_str)) => {
                path = Some(path_str.parse()?);
            }
            Some(other) => return Err(other.unexpected()).context("unexpected argument"),
            _ => (),
        }

        let Some(path) = path else {
            anyhow::bail!("missing argument <FILE_PATH>");
        };

        Ok(Self { path })
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::from_env()?;

    let mut files = SimpleFiles::new();
    files.add("[internally generated code]".to_string(), "");

    let before = Instant::now();

    let module = sugared::Module::load_from_path(&args.path, &mut files)?;

    let checked_module_res = process_root_module(module, &args.path, &mut files);

    let after = Instant::now();
    println!("total: {} ms", (after - before).as_millis());

    let checked_module = match checked_module_res {
        Ok(md) => md,
        Err(e) => {
            e.emit(&files)?;
            return Ok(());
        }
    };

    // if let Some(target_path) = args.type_of {
    //     let components: Vec<Ident> = target_path.split('.').map(Ident::from_str).collect();
    //     let target_path = ast::Path { components };

    //     println!("type of `{target_path}`:");
    //     println!(
    //         "    {}",
    //         target_path
    //             .to_expr(0)
    //             .ty(&checked_module, &Context::Empty, 0)
    //             .expect("module should be type-checked")
    //     );
    // }

    Ok(())
}

fn process_root_module(
    module: sugared::Module,
    path: &std::path::Path,
    files: &mut SimpleFiles<String, &str>,
) -> crate::err::Result<desugared::Module> {
    let root_mod_name = Ident::from_str("Lib");

    let mut desugared_module = module.desugared(&root_mod_name)?;

    desugared_module.bind_vars();

    desugared_module.load_submodules(&root_mod_name, path, files)?;

    desugared_module.topological_sort()?;

    let checked_module = desugared_module.type_check_root()?;

    println!("{}", "type checking successful".green().bold());

    Ok(checked_module)
}
