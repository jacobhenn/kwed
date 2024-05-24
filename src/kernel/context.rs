use crate::ast::{
    desugared::{Expr, Param},
    Ident,
};

use std::rc::Rc;

use anyhow::{bail, Result};

use uuid::Uuid;

#[derive(Clone, Debug)]
pub enum Context {
    Empty,
    Var { outer: Rc<Self>, id: Uuid, ty: Expr },
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
            Context::Empty => None,
            Context::Var { outer, id, ty } => {
                if *id == search_id {
                    Some(ty)
                } else {
                    outer.ty_of_var(search_id)
                }
            }
        }
    }
}
