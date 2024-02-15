use std::ops::Range;

use anyhow::Result;

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};

pub fn emit_one<'files>(
    message: &str,
    file_id: usize,
    span: Range<usize>,
    files: &SimpleFiles<&str, &str>,
) -> Result<()> {
    let diagnostic = Diagnostic::error()
        .with_message(message)
        .with_labels(vec![Label::primary(file_id, span)]);

    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, files, &diagnostic)?;

    Ok(())
}
