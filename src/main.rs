#![feature(iter_intersperse)]
#![feature(exact_size_is_empty)]
#![feature(assert_matches)]
#![feature(let_chains)]
#![feature(round_char_boundary)]
#![feature(iter_chain)]
#![allow(irrefutable_let_patterns)]

mod ast;

mod err;

mod parse;

mod kernel;

use crate::ast::sugared;

use std::{mem, path::PathBuf};

use argh::FromArgs;
use ast::{desugared, Ident};
use codespan_reporting::files::SimpleFiles;
use kernel::context::Context;

#[derive(FromArgs, Debug)]
/// Type-checker for the kwed proof language (see https://github.com/jacobhenn/kwed).
struct Args {
    /// path to the kwed module to type-check
    #[argh(positional)]
    path: PathBuf,

    // TODO: turn this into a subcommand
    /// print the type of an item in the given module. provide a fully qualified path
    #[argh(option)]
    type_of: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let args: Args = argh::from_env();

    let mut files = SimpleFiles::new();
    files.add("[internally generated code]".to_string(), "");

    let module = sugared::Module::load_from_path(&args.path, &mut files)?;

    let checked_module = match process_root_module(module, &args.path, &mut files) {
        Ok(md) => md,
        Err(e) => {
            e.emit(&files)?;
            return Ok(());
        }
    };

    if let Some(target_path) = args.type_of {
        let components: Vec<Ident> = target_path.split('.').map(Ident::from_str).collect();
        let target_path = ast::Path { components };

        println!("type of `{target_path}`:");
        println!(
            "    {}",
            target_path
                .to_expr(0)
                .ty(&checked_module, &Context::Empty, 0)
                .expect("module should be type-checked")
        );
    }

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

    println!("type checking successful");

    Ok(checked_module)
}
