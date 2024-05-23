#![feature(iter_intersperse)]

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

    let module = match ast::sugared::Module::parse_final().parse_recovery(src.as_str()) {
        (Some(module), _errs) => module,
        (None, errs) => {
            err::emit(errs, file_id, &files)?;
            return Ok(());
        }
    };

    debug!("parsed module: {module:#?}");

    let mut desugared_module = module.desugared();

    debug!("desugared module: {desugared_module:#?}");

    desugared_module.bind_vars()?;

    debug!("desugared module with variables bound: {desugared_module:#?}");

    let mut checked_module = Module::new();

    for (name, mut item) in desugared_module.items {
        item.type_check(&checked_module)?;
        item.eval(&checked_module)?;

        checked_module.items.insert(name, item);
    }

    info!("type checking successful");

    Ok(())
}
