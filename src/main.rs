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

use ast::Ident;
use clap::Parser as _;
use codespan_reporting::files::SimpleFiles;
use tracing::{debug, info, Level};

#[derive(clap::Parser, Debug)]
/// Type-checker for the kwed proof language (see https://github.com/jacobhenn/kwed).
struct Args {
    /// path to the kwed module to type-check
    path: PathBuf,
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

    if let Err(e) = process_root_module(module, &args.path, &mut files) {
        e.emit(&files)?;
    }

    Ok(())
}

fn process_root_module(
    module: sugared::Module,
    path: &std::path::Path,
    files: &mut SimpleFiles<String, &str>,
) -> crate::err::Result<()> {
    let root_mod_name = Ident::from_str("Lib");

    let mut desugared_module = module.desugared(&root_mod_name)?;

    debug!("desugared module: {desugared_module}");

    desugared_module.bind_vars();

    debug!("module with variables bound: {desugared_module}");

    desugared_module.load_submodules(&root_mod_name, path, files)?;

    debug!("module with submodules loaded: {desugared_module}");

    desugared_module.topological_sort()?;

    debug!("module with items topologically sorted: {desugared_module}");

    desugared_module.type_check_root()?;

    info!("type checking successful");

    Ok(())
}
