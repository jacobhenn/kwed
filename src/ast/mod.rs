pub mod bind_vars;

pub mod sugared;

pub mod desugared;

use std::{fmt::Display, ops::Range, path::PathBuf};

#[derive(PartialEq, Eq, Debug, Hash, Clone, Default)]
pub struct Span {
    pub file: PathBuf,
    pub range: Range<usize>,
}

#[derive(PartialEq, Eq, Debug, Hash, Clone, Default)]
pub struct Ident {
    pub name: String,
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct Path {
    pub components: Vec<Ident>,
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
