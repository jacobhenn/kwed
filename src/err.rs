use crate::ast::Span;

use std::{fmt::Write, ops::Range};

use chumsky::{error::SimpleReason, prelude::Simple};

use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};

use tracing::debug;

fn convert_span(src: &str, mut span: Range<usize>) -> Range<usize> {
    let start = src
        .char_indices()
        .skip(span.start.saturating_sub(1))
        .find(|(_, c)| !c.is_whitespace())
        .map(|(i, _)| i)
        .unwrap_or(src.len());

    while src.chars().nth(span.end - 1).unwrap().is_whitespace() {
        span.end -= 1;
    }

    let end = src.char_indices().nth(span.end).unwrap().0;

    start..end
}

#[derive(Debug)]
pub struct Error {
    pub span: Option<Span>,
    pub message: String,
    pub labels: Vec<(Option<Span>, String)>,
    pub notes: Vec<String>,
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

#[macro_export]
macro_rules! err {
    ( $span:expr, $fmt:literal $(, $($arg:expr),+)? $(; $secondary_span: expr, $secondary_fmt:literal $(, $($secondary_arg:expr),+)?)* $(; @note $note_fmt:literal $(, $($note_arg:expr),+)?)* ) => {
        $crate::err::Error {
            span: $span,
            message: format!($fmt, $($($arg),+)?),
            labels: vec![$(($secondary_span, format!($secondary_fmt, $($($secondary_arg),+)?))),*],
            notes: vec![$((format!($note_fmt, $($($note_arg),+)?))),*],
        }
    };
}

#[macro_export]
macro_rules! bail {
    ( $span:expr, $fmt:literal $(, $($arg:expr),+)? $(; $secondary_span: expr, $secondary_fmt:literal $(, $($secondary_arg:expr),+)?)* $(; @note $note_fmt:literal $(, $($note_arg:expr),+)?)* ) => {
        return Err($crate::err!($span, $fmt $(, $($arg),+)? $(; $secondary_span, $secondary_fmt $(, $($secondary_arg),+)?)* $(; @note $note_fmt $(, $($note_arg),+)?)*))
    }
}

impl Error {
    fn convert_spans<'files>(&mut self, files: &SimpleFiles<String, &str>) {
        if let Some(span) = &mut self.span {
            let src = files
                .get(span.file_id)
                .expect("file id should be valid")
                .source();

            span.range = convert_span(src, span.range.clone());
        }

        for (span, _) in &mut self.labels {
            if let Some(span) = span {
                let src = files
                    .get(span.file_id)
                    .expect("file id should be valid")
                    .source();

                span.range = convert_span(src, span.range.clone());
            }
        }
    }

    pub fn emit<'files>(mut self, files: &SimpleFiles<String, &str>) -> anyhow::Result<()> {
        self.convert_spans(files);

        let mut labels = Vec::new();

        if let Some(span) = &self.span {
            labels.push(Label::primary(span.file_id, span.range.clone()));
        }

        for (span, msg) in self.labels {
            if let Some(span) = span {
                labels.push(Label::secondary(span.file_id, span.range.clone()).with_message(msg));
            }
        }

        let diagnostic = Diagnostic::error()
            .with_message(self.message)
            .with_labels(labels)
            .with_notes(self.notes);

        let writer = StandardStream::stderr(ColorChoice::Auto);
        let mut config = codespan_reporting::term::Config::default();
        config.chars = codespan_reporting::term::Chars::ascii();

        term::emit(&mut writer.lock(), &config, files, &diagnostic)?;

        Ok(())
    }
}

pub fn emit_parse_err<'files>(
    errs: impl IntoIterator<Item = Simple<char>>,
    file_id: usize,
    files: &SimpleFiles<String, &str>,
) {
    let src = files
        .get(file_id)
        .expect("file id should be valid")
        .source();

    for err in errs {
        let diagnostic = match err.reason() {
            SimpleReason::Unexpected => {
                let mut message = "Expected any of [ ".to_string();

                for &expected in err.expected().filter_map(|e| e.as_ref()) {
                    write!(message, "`{expected}` ").unwrap();
                }

                write!(message, "]").unwrap();

                if let Some(found) = err.found() {
                    write!(message, " but found `{found}`").unwrap();
                }

                if let Some(label) = err.label() {
                    write!(message, " while parsing {label}").unwrap();
                }

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, convert_span(src, err.span()))])
            }
            SimpleReason::Unclosed { span, delimiter } => {
                let message = format!("Unclosed `{delimiter}`");

                let label_msg = "Opened here".to_string();

                Diagnostic::error().with_message(message).with_labels(vec![
                    Label::primary(file_id, convert_span(src, err.span())),
                    Label::secondary(file_id, convert_span(src, span.clone()))
                        .with_message(label_msg),
                ])
            }
            SimpleReason::Custom(custom_msg) => {
                let mut message = String::new();

                if let Some(label) = err.label() {
                    write!(message, "while parsing {label}: ").unwrap();
                }

                write!(message, "{custom_msg}").unwrap();

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, convert_span(src, err.span()))])
            }
        };

        let writer = StandardStream::stderr(ColorChoice::Auto);
        let mut config = codespan_reporting::term::Config::default();
        config.chars = codespan_reporting::term::Chars::ascii();
        term::emit(&mut writer.lock(), &config, files, &diagnostic)
            .expect("error can be emitted to stdout");
    }
}
