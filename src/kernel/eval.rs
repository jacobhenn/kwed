use std::{os::unix::thread::JoinHandleExt, rc::Rc};

use crate::{
    ast::desugared::{Expr, Item, Module},
    kernel::context::Context,
};

use anyhow::{bail, Context as _, Result};

use tracing::{instrument, trace};

impl Expr {
    /// Substitute the expression `sub` for the free variable in `self`. `self` is assumed to
    /// contain a single free variable, as the body of a function.
    #[instrument(level = "trace", fields(self = %self, sub = %sub))]
    fn substitute_impl(&mut self, sub: &Expr, idx: usize) {
        match self {
            Expr::TypeType => (),
            Expr::Var(i) => {
                if *i == idx {
                    *self = sub.clone()
                }
            }
            Expr::Path(_) => (),
            Expr::Fn { param, body } => {
                Rc::make_mut(param).ty.substitute_impl(sub, idx);
                Rc::make_mut(body).substitute_impl(sub, idx + 1);
            }
            Expr::FnType { param, cod } => {
                Rc::make_mut(param).ty.substitute_impl(sub, idx);
                Rc::make_mut(cod).substitute_impl(sub, idx + 1);
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).substitute_impl(sub, idx);
                Rc::make_mut(arg).substitute_impl(sub, idx);
            }
            Expr::Eq { lhs, rhs } => {
                Rc::make_mut(lhs).substitute_impl(sub, idx);
                Rc::make_mut(rhs).substitute_impl(sub, idx);
            }
            Expr::Refl(arg) => Rc::make_mut(arg).substitute_impl(sub, idx),
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }

    pub fn substitute(&mut self, sub: &Expr) {
        self.substitute_impl(sub, 0)
    }

    pub fn contains_var(&self, idx: usize) -> bool {
        match self {
            Expr::TypeType => false,
            Expr::Var(i) => *i == idx,
            Expr::Path(_) => false,
            Expr::Fn { param, body } => param.ty.contains_var(idx) || body.contains_var(idx + 1),
            Expr::FnType { param, cod } => param.ty.contains_var(idx) || cod.contains_var(idx + 1),
            Expr::FnApp { func, arg } => func.contains_var(idx) || arg.contains_var(idx),
            Expr::Eq { lhs, rhs } => lhs.contains_var(idx) || rhs.contains_var(idx),
            Expr::Refl(arg) => arg.contains_var(idx),
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }

    fn decrement_vars(&mut self, cutoff: usize) {
        match self {
            Expr::TypeType => (),
            Expr::Var(idx) => {
                if *idx > cutoff {
                    *idx -= 1;
                }
            }
            Expr::Path(_) => (),
            Expr::Fn { param, body } => {
                Rc::make_mut(param).ty.decrement_vars(cutoff);
                Rc::make_mut(body).decrement_vars(cutoff + 1);
            }
            Expr::FnType { param, cod } => {
                Rc::make_mut(param).ty.decrement_vars(cutoff);
                Rc::make_mut(cod).decrement_vars(cutoff + 1);
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).decrement_vars(cutoff);
                Rc::make_mut(arg).decrement_vars(cutoff);
            }
            Expr::Eq { lhs, rhs } => {
                Rc::make_mut(lhs).decrement_vars(cutoff);
                Rc::make_mut(rhs).decrement_vars(cutoff);
            }
            Expr::Refl(arg) => {
                Rc::make_mut(arg).decrement_vars(cutoff);
            }
            Expr::Match { arg, cod, arms } => todo!(),
        }
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn eval(&mut self, md: &Module, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType => (),
            Expr::Var(_) => (),
            Expr::Path(path) => {
                let Item::Def { val, .. } = md
                    .items
                    .get(path)
                    .with_context(|| format!("could not find `{path}` in this scope"))?;

                *self = val.clone();
            }
            Expr::Fn { param, body } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(body).eval(md, ctx)?;

                // η-reduction: `[x] f x` reduces to `f` wherever `x` does not occur free in `f`.
                if let Expr::FnApp { func, arg } = Rc::make_mut(body) {
                    if let Expr::Var(0) = **arg {
                        if !func.contains_var(0) {
                            Rc::make_mut(func).decrement_vars(0);
                            *self = (**func).clone();
                        }
                    }
                }
            }
            Expr::FnType { param, cod } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(cod).eval(md, ctx)?;
            }
            Expr::FnApp { func, arg } => {
                Rc::make_mut(func).eval(md, ctx)?;
                if let Expr::Fn { param, body } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(arg);
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
