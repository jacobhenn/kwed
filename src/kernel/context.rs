use crate::ast::{
    desugared::{uuid_color, Expr},
    Path,
};

use std::{fmt::Display, rc::Rc};

use crossterm::style::Stylize;

use uuid::Uuid;

#[derive(Clone, Debug)]
pub enum Context {
    Empty,
    Var {
        outer: Rc<Self>,
        id: Uuid,
        ty: Expr,
    },
    Rec {
        outer: Rc<Self>,
        id: Uuid,
        ty: Expr,
    },
    ThisInductive {
        outer: Rc<Self>,
        path: Path,
        ty: Expr,
    },
}

impl Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Context::Empty => Ok(()),
            Context::Var { outer, id, .. } => write!(f, "{outer} {}", "●".with(uuid_color(*id))),
            Context::Rec { outer, id, .. } => {
                write!(f, "{outer} rec{{{}}}", "●".with(uuid_color(*id)))
            }
            Context::ThisInductive { outer, path, .. } => write!(f, "{outer} {{inductive {path}}}"),
        }
    }
}

impl Context {
    pub fn with_var(self, id: Uuid, ty: Expr) -> Self {
        Self::Var {
            outer: Rc::new(self),
            id,
            ty,
        }
    }

    pub fn ty_of_var(&self, search_id: Uuid) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Var { outer, id, ty } => {
                if *id == search_id {
                    Some(ty)
                } else {
                    outer.ty_of_var(search_id)
                }
            }
            Self::ThisInductive { outer, .. } | Self::Rec { outer, .. } => {
                outer.ty_of_var(search_id)
            }
        }
    }

    pub fn ty_of_rec_var(&self, search_id: Uuid) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Rec { outer, id, ty } => {
                if *id == search_id {
                    Some(ty)
                } else {
                    outer.ty_of_var(search_id)
                }
            }
            Self::Var { outer, .. } | Self::ThisInductive { outer, .. } => {
                outer.ty_of_rec_var(search_id)
            }
        }
    }

    pub fn this_inductive(&self) -> Option<(&Path, &Expr)> {
        match self {
            Self::Empty => None,
            Self::ThisInductive { path, ty, .. } => Some((path, ty)),
            Self::Var { outer, .. } | Self::Rec { outer, .. } => outer.this_inductive(),
        }
    }
}
