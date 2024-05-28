#![feature(iter_intersperse)]
#![feature(exact_size_is_empty)]
#![feature(assert_matches)]
#![feature(let_chains)]

mod ast;

mod err;

mod parse;

mod kernel;

use crate::ast::desugared::Module;

use std::fs;

use anyhow::Result;

use chumsky::Parser;

use codespan_reporting::files::SimpleFiles;

use tracing::{debug, info};

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .without_time()
        .with_file(true)
        .with_line_number(true)
        .pretty()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .with_span_events(tracing_subscriber::fmt::format::FmtSpan::ENTER)
        .init();

    let path = std::env::args().skip(1).next().unwrap();

    let src = fs::read_to_string(&path).unwrap();

    let mut files: SimpleFiles<&str, &str> = SimpleFiles::new();
    let file_id = files.add(&path, &src);

    let (module, errs) = ast::sugared::Module::parse_final().parse_recovery_verbose(src.as_str());

    if !errs.is_empty() {
        debug!("recovered AST: {module:#?}");

        err::emit_parse_err(errs, file_id, &files)?;
        return Ok(());
    };

    let module = module.expect("errorless parsing should be successful");

    debug!("parsed module: {module:#?}");

    let mut desugared_module = module.desugared();

    debug!("desugared module: {desugared_module:#?}");

    desugared_module.bind_vars()?;

    debug!("desugared module with variables bound: {desugared_module:#?}");

    let mut checked_module = Module::new();

    for (path, item) in desugared_module.items {
        item.type_check(&path, &checked_module)?;
        item.eval_and_insert(path, &mut checked_module)?;
    }

    info!("type checking successful");

    Ok(())
}
