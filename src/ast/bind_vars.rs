use super::{
    desugared::{Expr, Item, MatchArm, Module},
    Ident,
};

use std::{mem, rc::Rc};

use anyhow::Result;

#[derive(Debug, Clone)]
enum Context {
    Empty,
    Var(Box<Self>, Ident),
}

impl Context {
    fn idx(&self, search_name: &Ident) -> Option<usize> {
        match self {
            Context::Empty => None,
            Context::Var(outer, name) => {
                if name == search_name {
                    Some(0)
                } else {
                    outer.idx(search_name).map(|i| i + 1)
                }
            }
        }
    }
}

impl Expr {
    fn bind_vars(&mut self, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType => (),
            Expr::Var(..) => (),
            Expr::Path(path) => {
                if let [name] = &mut path.components[..] {
                    if let Some(idx) = ctx.idx(name) {
                        *self = Self::Var(idx);
                    }
                }
            }
            Expr::Fn { param, body } => {
                Rc::make_mut(param).ty.bind_vars(&ctx)?;

                let ctx = Context::Var(Box::new(ctx.clone()), param.name.clone());

                Rc::make_mut(body).bind_vars(&ctx)?;
            }
            Expr::FnType { param, cod } => {
                Rc::make_mut(param).ty.bind_vars(ctx)?;

                let ctx = Context::Var(Box::new(ctx.clone()), param.name.clone());

                Rc::make_mut(cod).bind_vars(&ctx)?;
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).bind_vars(ctx)?;
                Rc::make_mut(arg).bind_vars(ctx)?;
            }
            Expr::Eq { lhs, rhs } => {
                Rc::make_mut(lhs).bind_vars(ctx)?;
                Rc::make_mut(rhs).bind_vars(ctx)?;
            }
            Expr::Refl(arg) => Rc::make_mut(arg).bind_vars(ctx)?,
            Expr::Match { arg, cod, arms } => {
                Rc::make_mut(arg).bind_vars(ctx)?;
                Rc::make_mut(cod).bind_vars(ctx)?;
                for arm in arms {
                    arm.body.bind_vars(ctx)?;
                }
            }
        }

        Ok(())
    }
}

impl Item {
    pub fn bind_vars(&mut self) -> Result<()> {
        match self {
            Item::Def { ty, val } => {
                ty.bind_vars(&Context::Empty)?;
                val.bind_vars(&Context::Empty)?;
            }
        }

        Ok(())
    }
}

impl Module {
    pub fn bind_vars(&mut self) -> Result<()> {
        for item in self.items.values_mut() {
            item.bind_vars()?;
        }

        Ok(())
    }
}
