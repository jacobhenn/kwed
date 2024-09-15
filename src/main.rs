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

use ast::{desugared, Ident};
use clap::Parser as _;
use codespan_reporting::files::SimpleFiles;
use kernel::context::Context;
use tracing::{debug, info, Level};

#[derive(clap::Parser, Debug)]
/// Type-checker for the kwed proof language (see https://github.com/jacobhenn/kwed).
struct Args {
    /// path to the kwed module to type-check
    path: PathBuf,

    /// print the type of an item in the given module. provide a fully qualified path
    #[arg(short, long)]
    type_of: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let env_filter = tracing_subscriber::EnvFilter::builder()
        .with_default_directive(Level::INFO.into())
        .from_env()?;

    tracing_subscriber::fmt()
        .without_time()
        .with_file(true)
        .with_line_number(true)
        .pretty()
        .with_env_filter(env_filter)
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::ENTER)
        .init();

    let args = Args::parse();

    let mut files = SimpleFiles::new();

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
                .to_expr()
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

    debug!("desugared module: {desugared_module}");

    desugared_module.bind_vars();

    debug!("module with variables bound: {desugared_module}");

    desugared_module.load_submodules(&root_mod_name, path, files)?;

    debug!("module with submodules loaded: {desugared_module}");

    desugared_module.topological_sort()?;

    debug!("module with items topologically sorted: {desugared_module}");

    let checked_module = desugared_module.type_check_root()?;

    info!("type checking successful");

    Ok(checked_module)
}
