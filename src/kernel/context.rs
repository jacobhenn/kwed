use crate::ast::{
    desugared::{id_color, Expr},
    Path,
};

use std::{fmt::Display, rc::Rc};

use yansi::Paint;

#[derive(Clone, Debug)]
pub enum Context {
    Empty,
    Var {
        outer: Rc<Self>,
        id: u128,
        ty: Expr,
    },
    RecTy {
        outer: Rc<Self>,
        id: u128,
        ty: Expr,
    },
    RecVal {
        outer: Rc<Self>,
        id: u128,
        val: Expr,
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
            Context::Var { outer, id, .. } => write!(f, "{outer} {}", "●".paint(id_color(*id))),
            Context::RecTy { outer, id, .. } => {
                write!(f, "{outer} (rec {})", "●".paint(id_color(*id)))
            }
            Context::RecVal { outer, id, .. } => {
                write!(f, "{outer} rec-val{{{}}}", "●".paint(id_color(*id)))
            }
            Context::ThisInductive { outer, path, .. } => write!(f, "{outer} {{inductive {path}}}"),
        }
    }
}

impl Context {
    pub fn with_var(self, id: u128, ty: Expr) -> Self {
        Self::Var {
            outer: Rc::new(self),
            id,
            ty,
        }
    }

    pub fn with_vars(self, vars: impl IntoIterator<Item = (u128, Expr)>) -> Self {
        vars.into_iter()
            .fold(self, |ctx, (id, ty)| ctx.with_var(id, ty))
    }

    pub fn with_rec_ty(self, id: u128, ty: Expr) -> Self {
        Self::RecTy {
            outer: Rc::new(self),
            id,
            ty,
        }
    }

    pub fn with_rec_val(self, id: u128, val: Expr) -> Self {
        Self::RecVal {
            outer: Rc::new(self),
            id,
            val,
        }
    }

    pub fn ty_of_var(&self, search_id: u128) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Var { outer, id, ty } => {
                if *id == search_id {
                    Some(ty)
                } else {
                    outer.ty_of_var(search_id)
                }
            }
            Self::ThisInductive { outer, .. }
            | Self::RecTy { outer, .. }
            | Self::RecVal { outer, .. } => outer.ty_of_var(search_id),
        }
    }

    pub fn ty_of_rec(&self, search_id: u128) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::RecTy { outer, id, ty } => {
                if *id == search_id {
                    Some(ty)
                } else {
                    outer.ty_of_rec(search_id)
                }
            }
            Self::ThisInductive { outer, .. }
            | Self::Var { outer, .. }
            | Self::RecVal { outer, .. } => outer.ty_of_rec(search_id),
        }
    }

    pub fn val_of_rec(&self, search_id: u128) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::RecVal { outer, id, val } => {
                if *id == search_id {
                    Some(val)
                } else {
                    outer.val_of_rec(search_id)
                }
            }
            Self::ThisInductive { outer, .. }
            | Self::Var { outer, .. }
            | Self::RecTy { outer, .. } => outer.val_of_rec(search_id),
        }
    }

    pub fn this_inductive(&self) -> Option<(&Path, &Expr)> {
        match self {
            Self::Empty => None,
            Self::ThisInductive { path, ty, .. } => Some((path, ty)),
            Self::Var { outer, .. } | Self::RecTy { outer, .. } | Self::RecVal { outer, .. } => {
                outer.this_inductive()
            }
        }
    }
}
