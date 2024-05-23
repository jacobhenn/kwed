use crate::ast::{
    desugared::{Expr, Param},
    Ident,
};

use std::rc::Rc;

use anyhow::{bail, Result};

#[derive(Clone, Debug)]
pub enum Context {
    Empty,
    Var(Rc<Self>, Ident, Expr),
}

impl Context {
    pub fn with_var(self, name: Ident, ty: Expr) -> Self {
        Self::Var(Rc::new(self), name, ty)
    }

    pub fn with_param(self, param: Param) -> Self {
        self.with_var(param.name, param.ty)
    }

    pub fn ty_of_var(&self, idx: usize) -> Option<&Expr> {
        match self {
            Context::Empty => None,
            Context::Var(outer, _name, ty) => {
                if idx == 0 {
                    Some(ty)
                } else {
                    outer.ty_of_var(idx - 1)
                }
            }
        }
    }
}
