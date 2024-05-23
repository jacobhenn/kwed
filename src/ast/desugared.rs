use super::{sugared, Ident, Path, Span};

use std::{cmp::Ordering, fmt::Display, rc::Rc};

use derivative::Derivative;

use indexmap::IndexMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    TypeType,

    Var(usize),
    Path(Path),

    Fn {
        param: Rc<Param>,
        body: Rc<Self>,
    },
    FnType {
        param: Rc<Param>,
        cod: Rc<Self>,
    },
    FnApp {
        func: Rc<Self>,
        arg: Rc<Self>,
    },

    Eq {
        lhs: Rc<Self>,
        rhs: Rc<Self>,
    },
    Refl(Rc<Self>),

    Match {
        arg: Rc<Self>,
        cod: Rc<Self>,
        arms: Vec<MatchArm>,
    },
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq)]
pub struct Param {
    #[derivative(PartialEq = "ignore")]
    pub name: Ident,
    pub ty: Expr,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MatchArm {
    pub constructor: Path,
    pub args: Vec<Ident>,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub enum Item {
    Def { ty: Expr, val: Expr },
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub items: IndexMap<Path, Item>,
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::TypeType => write!(f, "Type"),
            Expr::Var(idx) => write!(f, "var{{{idx}}}"),
            Expr::Path(path) => write!(f, "{path}"),
            Expr::Fn { param, body } => write!(f, "[{param}] {body}"),
            Expr::FnType { param, cod } => write!(f, "({param}) -> {cod}"),
            Expr::FnApp { func, arg } => write!(f, "({func}) ({arg})"),
            Expr::Eq { lhs, rhs } => write!(f, "({lhs}) = ({rhs})"),
            Expr::Refl(arg) => write!(f, "refl {arg}"),
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Def { ty, val } => write!(f, "def _: {ty} {{ {val} }}"),
        }
    }
}

impl Module {
    pub fn new() -> Self {
        Self {
            items: IndexMap::new(),
        }
    }
}
