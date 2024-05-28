use std::rc::Rc;

use crate::{
    ast::{
        desugared::{Expr, Item, Module},
        Path,
    },
    kernel::context::Context,
};

use anyhow::Result;

use tracing::{instrument, trace};

use uuid::Uuid;

impl Expr {
    pub fn substitute(&mut self, target_id: Uuid, sub: &Expr) {
        match self {
            Expr::TypeType | Expr::Rec { .. } => (),
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
            Expr::Match { arg, cod, arms } => {
                Rc::make_mut(arg).substitute(target_id, sub);
                Rc::make_mut(cod).substitute(target_id, sub);
                for arm in arms {
                    arm.body.substitute(target_id, sub);
                }
            }
        }
    }

    pub fn contains_var(&self, search_id: Uuid) -> bool {
        match self {
            Expr::TypeType | Expr::Rec { .. } => false,
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
            Expr::Match { arg, cod, arms } => {
                arg.contains_var(search_id)
                    || cod.contains_var(search_id)
                    || arms.iter().any(|arm| arm.body.contains_var(search_id))
            }
        }
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn eval(&mut self, md: &Module, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType | Expr::Rec { .. } => (),
            Expr::Var { .. } => (),
            Expr::Path(path) => {
                if let Some(Item::Def { val, .. }) = md.items.get(path) {
                    *self = val.clone();
                }
            }
            Expr::Fn { param, body } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(body).eval(md, ctx)?;

                // η-reduction: `[x] f x` reduces to `f` wherever `x` does not occur free in `f`.
                if let Expr::FnApp { func, arg } = Rc::make_mut(body) {
                    if let Expr::Var { id: arg_id, .. } = **arg {
                        if arg_id == param.id && !func.contains_var(param.id) {
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
                if let Expr::Fn { param, body } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(param.id, arg);
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
    pub fn eval_and_insert(mut self, path: Path, md: &mut Module) -> Result<()> {
        match &mut self {
            Item::Def { ty, val } => {
                ty.eval(md, &Context::Empty)?;
                val.eval(md, &Context::Empty)?;
            }
            Item::Axiom { ty } => ty.eval(md, &Context::Empty)?,
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                let mut ctx = Context::Empty;

                for param in params {
                    param.ty.eval(md, &ctx)?;
                    ctx = ctx.with_var(param.id, param.ty.clone());
                }

                ty.eval(md, &ctx)?;

                for constructor in constructors {
                    constructor.ty.eval(md, &ctx)?;
                }
            }
        }

        md.items.insert(path, self);

        Ok(())
    }
}
