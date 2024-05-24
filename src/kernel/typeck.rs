use std::rc::Rc;

use crate::{
    ast::{
        desugared::{Expr, Item, Module},
        Ident,
    },
    kernel::context::Context,
};

use anyhow::{bail, Context as _, Result};

use base64::prelude::*;

use tracing::{instrument, trace};
use uuid::Uuid;

impl Expr {
    #[instrument(level = "trace", skip(md, ctx), fields(self = %self, expected = %expected))]
    fn expect_ty(&self, expected: &Self, md: &Module, ctx: &Context) -> Result<()> {
        let mut expected = expected.clone();
        expected.eval(md, ctx)?;

        let mut found = self.ty(md, ctx)?;
        found.eval(md, ctx)?;

        if !Self::eq_up_to_vars(&expected, &found) {
            bail!("mismatched types: expected `{expected}`, found `{found}`");
        }
        Ok(())
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn ty(&self, md: &Module, ctx: &Context) -> Result<Self> {
        use Expr::*;
        let res = match self {
            TypeType => TypeType,
            Var { id, .. } => ctx
                .ty_of_var(*id)
                .expect("variables are bound correctly")
                .clone(),
            Path(path) => match md
                .items
                .get(path)
                .with_context(|| format!("could not find `{path}` in this scope"))?
            {
                Item::Def { ty, .. } => ty.clone(),
            },
            Fn { param, id, body } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;

                let mut body = (**body).clone();
                let new_id = Uuid::new_v4();
                body.substitute(
                    *id,
                    &Expr::Var {
                        id: new_id,
                        name: param.name.clone(),
                    },
                );

                FnType {
                    param: param.clone(),
                    id: new_id,
                    cod: Rc::new(body.ty(md, &ctx.clone().with_var(new_id, param.ty.clone()))?),
                }
            }
            FnType { param, id, cod } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;

                let ctx = ctx.clone().with_var(*id, param.ty.clone());
                cod.expect_ty(&TypeType, md, &ctx)?;

                TypeType
            }
            FnApp { func, arg } => {
                // TODO: do i have to evaluate this?
                let func_type = func.ty(md, ctx)?;
                let FnType { param, cod, .. } = func_type else {
                    bail!("expected function");
                };

                arg.expect_ty(&param.ty, md, ctx)?;

                Rc::unwrap_or_clone(cod)
            }
            Eq { lhs, rhs } => {
                let lhs_ty = lhs.ty(md, ctx)?;
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
