use std::{iter, rc::Rc};

use crate::{
    ast::{
        desugared::{BindingParam, Expr, Item, MatchArm, Module, Param},
        Path, Span,
    },
    bail,
    err::Result,
    kernel::context::Context,
};

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
            bail!(
                self.span(),
                "mismatched types: expected `{expected}`, found `{found}`";
                expected.span(),
                "expected this"
            );
        }
        Ok(())
    }

    // TODO: verify assumption that this returns exprs in normal form
    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self, ctx = %ctx))]
    pub fn ty(&self, md: &Module, ctx: &Context) -> Result<Self> {
        use Expr::*;
        let res = match self {
            TypeType { .. } => TypeType { span: None },
            Var { id, .. } => ctx
                .ty_of_var(*id)
                .expect("variables are bound correctly")
                .clone(),
            Rec { id, .. } => ctx
                .ty_of_rec_var(*id)
                .expect("recursive calls are bound correctly")
                .clone(),
            Path { path, span } => {
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
                            span: None,
                        })
                } else if let Some((ind_path, ty)) = ctx.this_inductive()
                    && path == ind_path
                {
                    ty.clone()
                } else {
                    bail!(span.clone(), "cannot find item `{path}` in this scope")
                }
            }

            Fn { param, body, .. } => {
                param.ty.expect_ty(&TypeType { span: None }, md, ctx)?;

                let mut body = (**body).clone();
                let new_id = Uuid::new_v4();
                body.substitute(
                    param.id,
                    &Expr::Var {
                        id: new_id,
                        name: param.name.clone(),
                        span: None,
                    },
                );

                FnType {
                    param: Rc::new(BindingParam {
                        id: new_id,
                        ..(**param).clone()
                    }),
                    cod: Rc::new(body.ty(md, &ctx.clone().with_var(new_id, param.ty.clone()))?),
                    span: None,
                }
            }
            FnType { param, cod, .. } => {
                param.ty.expect_ty(&TypeType { span: None }, md, ctx)?;

                let ctx = ctx.clone().with_var(param.id, param.ty.clone());
                cod.expect_ty(&TypeType { span: None }, md, &ctx)?;

                TypeType { span: None }
            }
            FnApp { func, arg, span } => {
                // TODO: do i have to evaluate this?
                let func_type = func.ty(md, ctx)?;
                let FnType { param, mut cod, .. } = func_type else {
                    bail!(span.clone(), "expected function");
                };

                arg.expect_ty(&param.ty, md, ctx)?;

                Rc::make_mut(&mut cod).substitute(param.id, arg);
                Rc::unwrap_or_clone(cod)
            }
            Match { arg, cod, arms, .. } => {
                let arg_ty = arg.ty(md, ctx)?;

                let Expr::Path {
                    path: arg_ty_head,
                    span: arg_ty_head_span,
                } = arg_ty.head()
                else {
                    bail!(
                        arg_ty.span(),
                        "cannot match on non-inductive type `{arg_ty}`"
                    )
                };

                let Some(arg_ty_head_item) = md.items.get(arg_ty_head) else {
                    bail!(
                        arg_ty_head_span.clone(),
                        "could not find `{arg_ty_head}` in this scope"
                    );
                };

                let Item::Inductive {
                    params: ind_def_params,
                    ty: ind_def_ty,
                    constructors: ind_def_constructors,
                } = arg_ty_head_item
                else {
                    bail!(
                        arg_ty_head_span.clone(),
                        "cannot match on non-inductive type `{arg_ty_head}`"
                    )
                };

                let cod_ty = cod.ty(md, ctx)?;

                debug!("cod_ty: {cod_ty}");

                let [index_params @ .., final_param] = &cod_ty.fn_ty_params()[..] else {
                    bail!(
                        cod.span(),
                        "expected match codomain to be a type family, found `{cod_ty}`"
                    )
                };

                debug!("final_param: {final_param:?}");

                debug!(
                    "index_params: {index_params:?}, ind_def_ty.fn_ty_params(): {:?}",
                    ind_def_ty.fn_ty_params()
                );

                // TODO: can i check this indirectly since I already know that final_param typecks?
                if !iter::zip(index_params, ind_def_ty.fn_ty_params())
                    .all(|(l, r)| Expr::eq_up_to_vars(&l.ty, &r.ty))
                {
                    bail!(
                        cod.span(),
                        "match codomain must have params for all indices of `{arg_ty_head}`"
                    );
                }

                if !Expr::eq_up_to_vars(final_param.ty.head(), arg_ty.head()) {
                    bail!(
                        final_param.ty.span(),
                        "match codomain must include parameter of type `{arg_ty_head} ..`"
                    );
                }

                let final_param_args = final_param.ty.args();
                let (param_args, index_args) = final_param_args.split_at(ind_def_params.len());

                debug!("param_args: {param_args:?}, index_args: {index_args:?}");

                if !iter::zip(
                    param_args,
                    arg_ty.args().into_iter().take(ind_def_params.len()),
                )
                .all(|(l, r)| Expr::eq_up_to_vars(l, r))
                {
                    bail!(
                        cod.span(),
                        "parameters of `{arg_ty_head}` differ in match argument and codomain"
                    );
                }

                debug!("index_params: {index_params:?}, index_args: {index_args:?}");

                if !iter::zip(index_params, index_args).all(|(par, arg)| arg.is_var_with_id(par.id))
                {
                    bail!(
                        cod.span(),
                        "indices of `{arg_ty_head}` differ from arguments of match codomain"
                    );
                }

                expect_exhaustive(arms, ind_def_constructors, self.span())?;

                for arm in arms {
                    let Some(constructor_def) = ind_def_constructors
                        .iter()
                        .find(|c| c.name == arm.constructor)
                    else {
                        bail!(self.span(), "no such constructor {}", arm.constructor);
                    };

                    let constructor_def_params = constructor_def.ty.fn_ty_params();

                    trace!(
                        "args, params: ({}) ({:?}, {:?})",
                        constructor_def.name,
                        arm.args,
                        constructor_def_params
                    );

                    if arm.args.len() != constructor_def_params.len() {
                        bail!(
                            self.span(),
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

fn expect_exhaustive(
    match_arms: &[MatchArm],
    ind_def_constructors: &[Param],
    match_span: Option<Span>,
) -> Result<()> {
    for ind_def_constructor in ind_def_constructors {
        match match_arms
            .iter()
            .filter(|arm| arm.constructor == ind_def_constructor.name)
            .count()
        {
            0 => bail!(
                match_span,
                "constructor `{}` is not matched",
                ind_def_constructor.name
            ),
            1 => (),
            2.. => bail!(
                match_span,
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
        Expr::TypeType { .. } => Ok(()),
        other => bail!(
            other.span(),
            "`{other}` is not valid here in the type of an inductive definition"
        ),
    }
}

fn is_expected_app_root(ty: &Expr, item_path: &Path, params: &[BindingParam]) -> bool {
    match params {
        [params_head @ .., last_param] => match ty {
            Expr::FnApp { func, arg, .. } => {
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
            if let Expr::Path { path, .. } = ty
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
        Expr::Path { path, .. } if path == item_path => Ok(()),
        other => bail!(
            other.span(),
            "`{other}` is not valid here in the type of a constructor"
        ),
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
                        span: None,
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
                    param
                        .ty
                        .expect_ty(&Expr::TypeType { span: None }, md, &ctx)?;
                    ctx = ctx.with_var(param.id, param.ty.clone());
                }

                expect_valid_inductive_def_ty(ty)?;

                ctx = Context::ThisInductive {
                    outer: Rc::new(ctx),
                    path: path.clone(),
                    ty: self.ty(),
                };

                for constructor in constructors {
                    constructor
                        .ty
                        .expect_ty(&Expr::TypeType { span: None }, md, &ctx)?;
                    expect_valid_constructor_ty(&constructor.ty, path, params)?;
                    // TODO: positivity checking
                }
            }
        }

        Ok(())
    }
}
