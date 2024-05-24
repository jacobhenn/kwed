use super::{
    desugared::{Expr, Item, MatchArm, Module},
    Ident,
};

use std::{mem, rc::Rc};

use anyhow::Result;

use uuid::Uuid;

#[derive(Debug, Clone)]
enum Context {
    Empty,
    Var {
        outer: Box<Self>,
        name: Ident,
        id: Uuid,
    },
}

impl Context {
    fn id(&self, search_name: &Ident) -> Option<Uuid> {
        match self {
            Context::Empty => None,
            Context::Var { outer, name, id } => {
                if name == search_name {
                    Some(*id)
                } else {
                    outer.id(search_name)
                }
            }
        }
    }
}

impl Expr {
    fn bind_vars(&mut self, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType => (),
            Expr::Var { .. } => (),
            Expr::Path(path) => {
                if let [name] = &mut path.components[..] {
                    if let Some(id) = ctx.id(name) {
                        *self = Self::Var {
                            id,
                            name: mem::take(name),
                        };
                    }
                }
            }
            Expr::Fn { param, id, body } => {
                Rc::make_mut(param).ty.bind_vars(&ctx)?;

                let ctx = Context::Var {
                    outer: Box::new(ctx.clone()),
                    name: param.name.clone(),
                    id: *id,
                };

                Rc::make_mut(body).bind_vars(&ctx)?;
            }
            Expr::FnType { param, id, cod } => {
                Rc::make_mut(param).ty.bind_vars(ctx)?;

                let ctx = Context::Var {
                    outer: Box::new(ctx.clone()),
                    name: param.name.clone(),
                    id: *id,
                };

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
