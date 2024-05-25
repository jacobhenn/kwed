use std::fmt::Write;

use anyhow::Result;

use chumsky::{error::SimpleReason, prelude::Simple};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};

pub fn emit_parse_err<'files>(
    errs: impl IntoIterator<Item = Simple<char>>,
    file_id: usize,
    files: &SimpleFiles<&str, &str>,
) -> Result<()> {
    let writer = StandardStream::stderr(ColorChoice::Auto);
    let config = codespan_reporting::term::Config::default();

    for err in errs {
        let diagnostic = match err.reason() {
            SimpleReason::Unexpected => {
                let mut message = "Expected any of [ ".to_string();

                for &expected in err.expected().filter_map(|e| e.as_ref()) {
                    write!(message, "`{expected}` ")?;
                }

                write!(message, "]")?;

                if let Some(found) = err.found() {
                    write!(message, " but found `{found}`")?;
                }

                if let Some(label) = err.label() {
                    write!(message, " while parsing {label}")?;
                }

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, err.span())])
            }
            SimpleReason::Unclosed { span, delimiter } => {
                let message = format!("Unclosed `{delimiter}`");

                let label_msg = "Opened here".to_string();

                Diagnostic::error().with_message(message).with_labels(vec![
                    Label::primary(file_id, err.span()),
                    Label::secondary(file_id, span.clone()).with_message(label_msg),
                ])
            }
            SimpleReason::Custom(custom_msg) => {
                let mut message = String::new();

                if let Some(label) = err.label() {
                    write!(message, "while parsing {label}: ")?;
                }

                write!(message, "{custom_msg}")?;

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, err.span())])
            }
        };

        term::emit(&mut writer.lock(), &config, files, &diagnostic)?;
    }

    Ok(())
}
