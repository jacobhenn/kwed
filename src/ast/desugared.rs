use super::{sugared, Ident, Path, Span};

use std::{cmp::Ordering, collections::HashSet, fmt::Display, rc::Rc};

use crossterm::style::{Color, Stylize};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    TypeType,

    Var {
        id: Uuid,
        name: Ident,
    },
    Path(Path),

    Fn {
        param: Rc<Param>,
        id: Uuid,
        body: Rc<Self>,
    },
    FnType {
        param: Rc<Param>,
        id: Uuid,
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

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
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

fn uuid_color(id: Uuid) -> Color {
    Color::Rgb {
        r: id.as_bytes()[0],
        g: id.as_bytes()[1],
        b: id.as_bytes()[2],
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::TypeType => write!(f, "Type"),
            Expr::Var { id, name } => write!(f, "{}", name.name.as_str().with(uuid_color(*id))),
            Expr::Path(path) => write!(f, "{path}"),
            Expr::Fn { param, id, body } => write!(
                f,
                "[{}: {}] {body}",
                param.name.name.as_str().with(uuid_color(*id)),
                param.ty,
            ),
            Expr::FnType { param, id, cod } => write!(
                f,
                "({}: {}) → {cod}",
                param.name.name.as_str().with(uuid_color(*id)),
                param.ty
            ),
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

impl Expr {
    fn eq_impl(this: &Self, that: &Self, ctx: &mut HashSet<[Uuid; 2]>) -> bool {
        match (this, that) {
            (Expr::TypeType, Expr::TypeType) => true,
            (Expr::Var { id: lid, .. }, Expr::Var { id: rid, .. }) => ctx.contains(&[*lid, *rid]),
            (Expr::Path(l), Expr::Path(r)) => l == r,
            (
                Expr::Fn {
                    param: lparam,
                    id: lid,
                    body: lbody,
                },
                Expr::Fn {
                    param: rparam,
                    id: rid,
                    body: rbody,
                },
            ) => {
                let params_eq = Self::eq_impl(&lparam.ty, &rparam.ty, ctx);

                ctx.insert([*lid, *rid]);
                let bodies_eq = Self::eq_impl(lbody, rbody, ctx);
                ctx.remove(&[*lid, *rid]);

                params_eq && bodies_eq
            }
            (
                Expr::FnType {
                    param: lparam,
                    id: lid,
                    cod: lcod,
                },
                Expr::FnType {
                    param: rparam,
                    id: rid,
                    cod: rcod,
                },
            ) => {
                let params_eq = Self::eq_impl(&lparam.ty, &rparam.ty, ctx);

                ctx.insert([*lid, *rid]);
                let cods_eq = Self::eq_impl(lcod, rcod, ctx);
                ctx.remove(&[*lid, *rid]);

                params_eq && cods_eq
            }
            (
                Expr::FnApp {
                    func: lfunc,
                    arg: larg,
                },
                Expr::FnApp {
                    func: rfunc,
                    arg: rarg,
                },
            ) => Self::eq_impl(lfunc, rfunc, ctx) && Self::eq_impl(larg, rarg, ctx),
            (
                Expr::Eq {
                    lhs: llhs,
                    rhs: lrhs,
                },
                Expr::Eq {
                    lhs: rlhs,
                    rhs: rrhs,
                },
            ) => Self::eq_impl(llhs, rlhs, ctx) && Self::eq_impl(lrhs, rrhs, ctx),
            (Expr::Refl(larg), Expr::Refl(rarg)) => Self::eq_impl(larg, rarg, ctx),
            (_, _) => false,
        }
    }

    pub fn eq_up_to_vars(this: &Self, that: &Self) -> bool {
        Self::eq_impl(this, that, &mut HashSet::new())
    }
}

impl Module {
    pub fn new() -> Self {
        Self {
            items: IndexMap::new(),
        }
    }
}
