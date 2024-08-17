pub mod bind_vars;

pub mod sugared;

pub mod desugared;

use std::{fmt::Display, ops::Range, path::PathBuf};

use base64::prelude::*;
use uuid::Uuid;

#[derive(PartialEq, Eq, Debug, Hash, Clone, Default)]
pub struct Span {
    pub file_id: usize,
    pub range: Range<usize>,
}

#[derive(Debug, Clone, Default)]
pub struct Ident {
    pub name: String,
    pub span: Option<Span>,
}

impl Ident {
    pub fn new(name: String) -> Self {
        Self { name, span: None }
    }

    pub fn from_str(name: &str) -> Self {
        Self {
            name: name.to_string(),
            span: None,
        }
    }

    pub fn blank() -> Self {
        Self::from_str("●")
    }

    pub fn from_id(id: Uuid) -> Self {
        let encoded = BASE64_STANDARD.encode(&id.as_bytes()[..3]);

        Self::new(encoded)
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Ident {}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct Path {
    pub components: Vec<Ident>,
}

impl Span {
    pub fn new(file_id: usize, range: Range<usize>) -> Self {
        Self { file_id, range }
    }
}

impl Path {
    pub fn parent(self) -> Self {
        let [parent_components @ .., _] = &self.components[..] else {
            panic!("paths should not be empty");
        };

        Self {
            components: parent_components.to_vec(),
        }
    }

    pub fn last_component(&self) -> &Ident {
        self.components.last().expect("paths are non-empty")
    }

    pub fn first_component(&self) -> &Ident {
        self.components.first().expect("paths are non-empty")
    }

    pub fn span(&self) -> Option<Span> {
        if let (Some(first_span), Some(last_span)) =
            (&self.first_component().span, &self.last_component().span)
        {
            Some(Span {
                file_id: first_span.file_id,
                range: first_span.range.start..last_span.range.end,
            })
        } else {
            None
        }
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.components
                .iter()
                .map(|ident| ident.name.as_str())
                .intersperse(".")
                .collect::<String>()
        )
    }
}
