use std::{iter, rc::Rc};

use crate::{
    ast::{
        desugared::{BindingParam, Expr, Item, MatchArm, Module, Param},
        Path,
    },
    kernel::context::Context,
};

use anyhow::{bail, Context as _, Result};

use tracing::{debug, instrument, trace};

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

    // TODO: verify assumption that this returns exprs in normal form
    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self, ctx = %ctx))]
    pub fn ty(&self, md: &Module, ctx: &Context) -> Result<Self> {
        use Expr::*;
        let res = match self {
            TypeType => TypeType,
            Var { id, .. } | Rec { id, .. } => ctx
                .ty_of_var(*id)
                .expect("variables are bound correctly")
                .clone(),
            Path(path) => {
                if let Some(item) = md.items.get(path) {
                    item.ty()
                } else if let Some(Item::Inductive {
                    params,
                    constructors,
                    ..
                }) = md.items.get(&path.clone().parent())
                    && let Some(param) = constructors
                        .iter()
                        .find(|c| &c.name == path.components.last().expect("paths are non-empty"))
                {
                    params
                        .iter()
                        .cloned()
                        .rfold(param.ty.clone(), |acc, par| FnType {
                            param: Rc::new(par),
                            cod: Rc::new(acc),
                        })
                } else if let Some((ind_path, ty)) = ctx.this_inductive()
                    && path == ind_path
                {
                    ty.clone()
                } else {
                    bail!("cannot find item `{path}` in this scope")
                }
            }

            Fn { param, body } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;

                let mut body = (**body).clone();
                let new_id = Uuid::new_v4();
                body.substitute(
                    param.id,
                    &Expr::Var {
                        id: new_id,
                        name: param.name.clone(),
                    },
                );

                FnType {
                    param: Rc::new(BindingParam {
                        id: new_id,
                        ..(**param).clone()
                    }),
                    cod: Rc::new(body.ty(md, &ctx.clone().with_var(new_id, param.ty.clone()))?),
                }
            }
            FnType { param, cod } => {
                param.ty.expect_ty(&TypeType, md, ctx)?;

                let ctx = ctx.clone().with_var(param.id, param.ty.clone());
                cod.expect_ty(&TypeType, md, &ctx)?;

                TypeType
            }
            FnApp { func, arg } => {
                // TODO: do i have to evaluate this?
                let func_type = func.ty(md, ctx)?;
                let FnType { param, mut cod, .. } = func_type else {
                    bail!("expected function");
                };

                arg.expect_ty(&param.ty, md, ctx)?;

                Rc::make_mut(&mut cod).substitute(param.id, arg);
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
            Match { arg, cod, arms } => {
                let arg_ty = arg.ty(md, ctx)?;

                let Expr::Path(arg_ty_head) = arg_ty.head() else {
                    bail!("cannot match on non-inductive type `{arg_ty}`")
                };

                let Item::Inductive {
                    params: ind_def_params,
                    ty: ind_def_ty,
                    constructors: ind_def_constructors,
                } = md
                    .items
                    .get(arg_ty_head)
                    .context("could not find `{arg_ty_head}` in this scope")?
                else {
                    bail!("cannot match on non-inductive type `{arg_ty_head}`")
                };

                let cod_ty = cod.ty(md, ctx)?;

                debug!("cod_ty: {cod_ty}");

                let [index_params @ .., final_param] = &cod_ty.fn_ty_params()[..] else {
                    bail!("expected match codomain to be a type family, found `{cod_ty}`")
                };

                // TODO: can i check this indirectly since I already know that final_param typecks?
                if !iter::zip(index_params, ind_def_ty.fn_ty_params()).all(|(l, r)| l.ty == r.ty) {
                    bail!("match codomain must have params for all indices of `{arg_ty_head}`");
                }

                if final_param.ty.head() != arg_ty.head() {
                    bail!("match codomain must include parameter of type `{arg_ty_head} ..`");
                }

                debug!("final_param: {final_param:?}");

                let final_param_args = final_param.ty.args();
                let (param_args, index_args) = final_param_args.split_at(ind_def_params.len());

                debug!("param_args: {param_args:?}, index_args: {index_args:?}");

                if !iter::zip(
                    param_args,
                    arg_ty.args().into_iter().take(ind_def_params.len()),
                )
                .all(|(l, r)| Expr::eq_up_to_vars(l, r))
                {
                    bail!("parameters of `{arg_ty_head}` differ in match argument and codomain");
                }

                debug!("index_params: {index_params:?}, index_args: {index_args:?}");

                if !iter::zip(index_params, index_args).all(|(par, arg)| arg.is_var_with_id(par.id))
                {
                    bail!("indices of `{arg_ty_head}` differ from arguments of match codomain");
                }

                expect_exhaustive(arms, ind_def_constructors)?;

                for arm in arms {
                    let constructor_def = ind_def_constructors
                        .iter()
                        .find(|c| c.name == arm.constructor)
                        .with_context(|| format!("no such constructor `{}`", arm.constructor))?;

                    let constructor_def_params = constructor_def.ty.fn_ty_params();

                    trace!(
                        "args, params: ({}) ({:?}, {:?})",
                        constructor_def.name,
                        arm.args,
                        constructor_def_params
                    );

                    if arm.args.len() != constructor_def_params.len() {
                        bail!(
                            "captured arguments of `{}` do not match definition",
                            arm.constructor
                        );
                    }

                    let arm_ctx = iter::zip(&arm.args, constructor_def_params)
                        .fold((*ctx).clone(), |acc, ((id, _name), par)| {
                            acc.with_var(*id, par.ty.clone())
                        });

                    let body_ty = arm.body.ty(md, &arm_ctx)?;
                }

                todo!()
            }
        };

        trace!("return: {res}");

        Ok(res)
    }
}

fn expect_exhaustive(match_arms: &[MatchArm], ind_def_constructors: &[Param]) -> Result<()> {
    for ind_def_constructor in ind_def_constructors {
        match match_arms
            .iter()
            .filter(|arm| arm.constructor == ind_def_constructor.name)
            .count()
        {
            0 => bail!("constructor `{}` is not matched", ind_def_constructor.name),
            1 => (),
            2.. => bail!(
                "constructor `{}` is matched more than once",
                ind_def_constructor.name
            ),
        }
    }

    Ok(())
}

fn expect_valid_inductive_def_ty(ty: &Expr) -> Result<()> {
    match ty {
        Expr::FnType { cod, .. } => expect_valid_inductive_def_ty(cod),
        Expr::TypeType => Ok(()),
        other => bail!("`{other}` is not valid here in the type of an inductive definition"),
    }
}

fn is_expected_app_root(ty: &Expr, item_path: &Path, params: &[BindingParam]) -> bool {
    match params {
        [params_head @ .., last_param] => match ty {
            Expr::FnApp { func, arg } => {
                if let Expr::Var { id, .. } = **arg
                    && id == last_param.id
                {
                    is_expected_app_root(func, item_path, &params_head)
                } else {
                    false
                }
            }
            _ => false,
        },
        [] => {
            if let Expr::Path(path) = ty
                && path == item_path
            {
                true
            } else {
                false
            }
        }
    }
}

fn expect_valid_constructor_ty(ty: &Expr, item_path: &Path, params: &[BindingParam]) -> Result<()> {
    match ty {
        Expr::FnType { cod, .. } => expect_valid_constructor_ty(cod, item_path, params),
        Expr::FnApp { func, .. } => {
            if is_expected_app_root(func, item_path, params) {
                Ok(())
            } else {
                expect_valid_constructor_ty(func, item_path, params)
            }
        }
        Expr::Path(path) if path == item_path => Ok(()),
        other => bail!("`{other}` is not valid here in the type of a constructor"),
    }
}

impl Item {
    pub fn ty(&self) -> Expr {
        match self {
            Item::Def { ty, .. } | Item::Axiom { ty } => ty.clone(),
            Item::Inductive { params, ty, .. } => {
                params
                    .iter()
                    .cloned()
                    .rfold(ty.clone(), |acc, param| Expr::FnType {
                        param: Rc::new(param),
                        cod: Rc::new(acc),
                    })
            }
        }
    }

    #[instrument(level = "trace", skip(self, md), fields(self = %self, path = %path))]
    pub fn type_check(&self, path: &Path, md: &Module) -> Result<()> {
        match self {
            Item::Def { ty, val } => val.expect_ty(ty, md, &Context::Empty)?,
            Item::Axiom { .. } => (),
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                let mut ctx = Context::Empty;
                for param in params {
                    param.ty.expect_ty(&Expr::TypeType, md, &ctx)?;
                    ctx = ctx.with_var(param.id, param.ty.clone());
                }

                expect_valid_inductive_def_ty(ty)?;

                ctx = Context::ThisInductive {
                    outer: Rc::new(ctx),
                    path: path.clone(),
                    ty: self.ty(),
                };

                for constructor in constructors {
                    constructor.ty.expect_ty(&Expr::TypeType, md, &ctx)?;
                    expect_valid_constructor_ty(&constructor.ty, path, params)?;
                    // TODO: positivity checking
                }
            }
        }

        Ok(())
    }
}
