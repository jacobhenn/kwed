use std::rc::Rc;

use crate::{
    ast::desugared::{Expr, Item, Module},
    kernel::context::Context,
};

use anyhow::{bail, Context as _, Result};

use tracing::{instrument, trace};

use uuid::Uuid;

impl Expr {
    pub fn substitute(&mut self, target_id: Uuid, sub: &Expr) {
        match self {
            Expr::TypeType => (),
            Expr::Var { id, .. } => {
                if *id == target_id {
                    *self = sub.clone()
                }
            }
            Expr::Path(_) => (),
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.substitute(target_id, sub);
                Rc::make_mut(body).substitute(target_id, sub);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.substitute(target_id, sub);
                Rc::make_mut(cod).substitute(target_id, sub);
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).substitute(target_id, sub);
                Rc::make_mut(arg).substitute(target_id, sub);
            }
            Expr::Eq { lhs, rhs } => {
                Rc::make_mut(lhs).substitute(target_id, sub);
                Rc::make_mut(rhs).substitute(target_id, sub);
            }
            Expr::Refl(arg) => Rc::make_mut(arg).substitute(target_id, sub),
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }

    pub fn contains_var(&self, search_id: Uuid) -> bool {
        match self {
            Expr::TypeType => false,
            Expr::Var { id, .. } => *id == search_id,
            Expr::Path(_) => false,
            Expr::Fn { param, body, .. } => {
                param.ty.contains_var(search_id) || body.contains_var(search_id)
            }
            Expr::FnType { param, cod, .. } => {
                param.ty.contains_var(search_id) || cod.contains_var(search_id)
            }
            Expr::FnApp { func, arg } => {
                func.contains_var(search_id) || arg.contains_var(search_id)
            }
            Expr::Eq { lhs, rhs } => lhs.contains_var(search_id) || rhs.contains_var(search_id),
            Expr::Refl(arg) => arg.contains_var(search_id),
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn eval(&mut self, md: &Module, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType => (),
            Expr::Var { .. } => (),
            Expr::Path(path) => {
                let Item::Def { val, .. } = md
                    .items
                    .get(path)
                    .with_context(|| format!("could not find `{path}` in this scope"))?;

                *self = val.clone();
            }
            Expr::Fn { param, id, body } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(body).eval(md, ctx)?;

                // η-reduction: `[x] f x` reduces to `f` wherever `x` does not occur free in `f`.
                if let Expr::FnApp { func, arg } = Rc::make_mut(body) {
                    if let Expr::Var { id: arg_id, .. } = **arg {
                        if arg_id == *id && !func.contains_var(*id) {
                            *self = (**func).clone();
                        }
                    }
                }
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(cod).eval(md, ctx)?;
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).eval(md, ctx)?;
                if let Expr::Fn { id, body, .. } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(*id, arg);
                    Rc::make_mut(body).eval(md, ctx)?;

                    *self = (**body).clone();
                } else {
                    Rc::make_mut(arg).eval(md, ctx)?;
                }
            }
            Expr::Eq { lhs, rhs } => {
                Rc::make_mut(lhs).eval(md, ctx)?;
                Rc::make_mut(rhs).eval(md, ctx)?;
            }
            Expr::Refl(arg) => {
                Rc::make_mut(arg).eval(md, ctx)?;
            }
            Expr::Match { arg, cod, arms } => todo!(),
        }

        trace!("result: {self}");

        Ok(())
    }
}

impl Item {
    pub fn eval(&mut self, md: &Module) -> Result<()> {
        match self {
            Item::Def { ty, val } => {
                ty.eval(md, &Context::Empty)?;
                val.eval(md, &Context::Empty)?;
            }
        }

        Ok(())
    }
}
