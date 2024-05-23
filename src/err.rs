use std::fmt::Write;

use anyhow::Result;

use chumsky::prelude::Simple;

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};

pub fn emit<'files>(
    errs: impl IntoIterator<Item = Simple<char>>,
    file_id: usize,
    files: &SimpleFiles<&str, &str>,
) -> Result<()> {
    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = codespan_reporting::term::Config::default();

    for err in errs {
        let mut message = "Expected any of [ ".to_string();
        for &expected in err.expected().filter_map(|e| e.as_ref()) {
            write!(message, "`{expected}` ")?;
        }

        if let Some(label) = err.label() {
            write!(message, "] while parsing {label}")?;
        }

        let diagnostic = Diagnostic::error()
            .with_message(message)
            .with_labels(vec![Label::primary(file_id, err.span())]);

        term::emit(&mut writer.lock(), &config, files, &diagnostic)?;
    }

    Ok(())
}
