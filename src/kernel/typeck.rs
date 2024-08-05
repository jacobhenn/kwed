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
                } else if let Some(Item::Inductive { constructors, .. }) =
                    md.items.get(&path.clone().parent())
                    && let Some(param) = constructors
                        .iter()
                        .find(|c| &c.name == path.components.last().expect("paths are non-empty"))
                {
                    param.ty.clone()
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
                        arg.span(),
                        "cannot match on non-inductive type `{arg_ty}`";
                        arg_ty.span(), "this type is not inductive"
                    )
                };

                let Some(arg_ty_head_item) = md.items.get(arg_ty_head) else {
                    bail!(
                        arg_ty_head_span.clone(),
                        "could not find `{arg_ty_head}` in this scope"
                    );
                };

                let Item::Inductive {
                    ty: ind_def_ty,
                    constructors: ind_def_constructors,
                } = arg_ty_head_item
                else {
                    bail!(
                        arg.span(),
                        "cannot match on non-inductive type `{arg_ty_head}`";
                        arg_ty_head_span.clone(), "this type is not inductive"
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

                if !final_param.ty.head().is_path_to(arg_ty_head) {
                    bail!(
                        final_param.ty.span(),
                        "match codomain must include parameter of type `{arg_ty_head} ..`"
                    );
                }

                let final_param_args = final_param.ty.args();

                debug!("index_params: {index_params:?}");

                if !iter::zip(index_params, final_param_args)
                    .all(|(par, arg)| arg.is_var_with_id(par.id))
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

                    let mut arm_ctx = ctx.clone();

                    for ((id, _name), arm_param) in iter::zip(&arm.args, constructor_def_params) {
                        arm_ctx = arm_ctx.with_var(*id, arm_param.ty.clone());

                        if arm_param.ty.head().is_path_to(arg_ty_head) {
                            todo!("bind recurisve vars")
                        }
                    }

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

impl Item {
    pub fn ty(&self) -> Expr {
        match self {
            Item::Def { ty, .. } | Item::Axiom { ty } | Item::Inductive { ty, .. } => ty.clone(),
        }
    }

    #[instrument(level = "trace", skip(self, md), fields(self = %self, path = %path))]
    pub fn type_check(&self, path: &Path, md: &Module) -> Result<()> {
        match self {
            Item::Def { ty, val } => val.expect_ty(ty, md, &Context::Empty)?,
            Item::Axiom { .. } => (),
            Item::Inductive { ty, constructors } => {
                expect_valid_inductive_def_ty(ty)?;

                let ctx = Context::ThisInductive {
                    outer: Rc::new(Context::Empty),
                    path: path.clone(),
                    ty: self.ty(),
                };

                for constructor in constructors {
                    constructor
                        .ty
                        .expect_ty(&Expr::TypeType { span: None }, md, &ctx)?;

                    if !constructor.ty.root_cod().head().is_path_to(path) {
                        bail!(
                            constructor.ty.root_cod().span(),
                            "Constructors must return the type they are constructing"
                        );
                    }

                    // TODO: positivity checking
                }
            }
        }

        Ok(())
    }
}
