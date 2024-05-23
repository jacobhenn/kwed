use std::rc::Rc;

use crate::{
    ast::desugared::{Expr, Item, Module},
    kernel::context::Context,
};

use anyhow::{bail, Context as _, Result};

use tracing::{instrument, trace};

impl Expr {
    #[instrument(level = "trace", skip(md, ctx), fields(self = %self, expected = %expected))]
    fn expect_ty(&self, expected: &Self, md: &Module, ctx: &Context) -> Result<()> {
        let mut expected = expected.clone();
        expected.eval(md, ctx)?;

        let mut found = self.ty(md, ctx)?;
        found.eval(md, ctx)?;

        if expected != found {
            bail!("mismatched types: expected `{expected}`, found `{found}`");
        }
        Ok(())
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn ty(&self, md: &Module, ctx: &Context) -> Result<Self> {
        use Expr::*;
        let res = match self {
            TypeType => TypeType,
            Var(idx) => ctx
                .ty_of_var(*idx)
                .expect("variables are bound correctly")
                .clone(),
            Path(path) => match md
                .items
                .get(path)
                .with_context(|| format!("could not find `{path}` in this scope"))?
            {
                Item::Def { ty, .. } => ty.clone(),
            },
            Fn { param, body } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;

                FnType {
                    param: param.clone(),
                    cod: Rc::new(body.ty(md, &ctx.clone().with_param((**param).clone()))?),
                }
            }
            FnType { param, cod } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;
                cod.expect_ty(&TypeType, md, ctx)?;

                TypeType
            }
            FnApp { func, arg } => {
                // TODO: do i have to evaluate this?
                let func_type = func.ty(md, ctx)?;
                let FnType { param, cod } = func_type else {
                    bail!("expected function");
                };

                arg.expect_ty(&param.ty, md, ctx)?;

                Rc::unwrap_or_clone(cod)
            }
            Eq { lhs, rhs } => {
                let lhs_ty = rhs.ty(md, ctx)?;
                rhs.expect_ty(&lhs_ty, md, ctx)?;

                TypeType
            }
            Refl(arg) => {
                arg.ty(md, ctx)?;

                Eq {
                    lhs: arg.clone(),
                    rhs: arg.clone(),
                }
            }
            Match { arg, cod, arms } => todo!(),
        };

        trace!("return: {res}");

        Ok(res)
    }
}

impl Item {
    #[instrument(level = "trace", skip(self, md), fields(self = %self))]
    pub fn type_check(&self, md: &Module) -> Result<()> {
        match self {
            Item::Def { ty, val } => val.expect_ty(ty, md, &Context::Empty),
        }
    }
}
