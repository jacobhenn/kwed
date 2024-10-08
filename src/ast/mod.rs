pub mod bind_vars;

pub mod sugared;

pub mod desugared;

use std::{cmp, fmt::Display, ops::Range};

#[derive(PartialEq, Eq, Debug, Hash, Clone, Default)]
pub struct Span {
    pub file_id: usize,
    pub range: Range<usize>,
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}..{}",
            self.file_id, self.range.start, self.range.end
        )
    }
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

    // pub fn from_id(id: Ulid) -> Self {
    //     Self::new(id.to_string())
    // }

    pub fn to_expr(self) -> desugared::Expr {
        Path::new(vec![self]).to_expr()
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

    pub fn hull_opts(lhs: Option<Self>, rhs: Option<Self>) -> Option<Self> {
        let (lhs, rhs) = (lhs?, rhs?);

        (lhs.file_id == rhs.file_id).then(|| Span {
            file_id: lhs.file_id,
            range: cmp::min(lhs.range.start, rhs.range.start)
                ..cmp::max(lhs.range.end, rhs.range.end),
        })
    }

    pub fn hull(lhs: Self, rhs: Self) -> Option<Self> {
        Self::hull_opts(Some(lhs), Some(rhs))
    }
}

impl Path {
    pub fn new(components: Vec<Ident>) -> Self {
        Self { components }
    }

    pub fn to_expr(self) -> desugared::Expr {
        self.into()
    }

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
        let last_span = self.components.last()?.span.as_ref()?;

        let mut suffix_spans = self
            .components
            .iter()
            .rev()
            .map_while(|c| c.span.as_ref().filter(|s| s.file_id == last_span.file_id));

        let last_span = suffix_spans.next()?;
        let first_span = suffix_spans.last().unwrap_or_else(|| last_span);

        Span::hull(first_span.clone(), last_span.clone())
    }

    pub fn with_prefix(mut self, prefix: Ident) -> Self {
        self.components.insert(0, prefix);
        self
    }

    pub fn with_suffix(mut self, suffix: Ident) -> Self {
        self.components.push(suffix);
        self
    }

    pub fn resolved_in(mut self, mod_name: &Ident) -> Self {
        match self.first_component().name.as_str() {
            "Lib" => self,
            "Super" => {
                self.components.remove(0);
                if mod_name.name == "Lib" {
                    self.components.insert(0, mod_name.clone());
                }
                self
            }
            _ => self.with_prefix(mod_name.clone()),
        }
    }
}

impl From<Path> for desugared::Expr {
    fn from(path: Path) -> Self {
        let span = path.span();
        Self::Path { path, span }
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

#[derive(Debug, PartialEq, Eq, Clone, serde::Deserialize)]
#[serde(default)]
pub struct Directives {
    pub type_in_type: bool,
    pub max_recursion_depth: Option<usize>,
}

impl Default for Directives {
    fn default() -> Self {
        Self {
            type_in_type: false,
            max_recursion_depth: Some(512),
        }
    }
}
