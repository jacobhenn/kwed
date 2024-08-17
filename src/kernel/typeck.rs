use std::{iter, rc::Rc};

use crate::{
    ast::{
        desugared::{BindingParam, Expr, Item, Module, Param},
        sugared, Ident, Path,
    },
    bail,
    err::Result,
    kernel::context::Context,
};

use tracing::{debug, instrument, trace};

use uuid::Uuid;

pub(super) fn recursible_param_idxs<'a>(
    ind_def_path: &'a Path,
    ind_def_params: &'a [BindingParam],
    constructor_ty: &'a Expr,
) -> impl Iterator<Item = usize> + 'a {
    constructor_ty
        .fn_ty_params()
        .into_iter()
        .enumerate()
        .filter(move |(_i, par)| {
            // A parameter is recursible iff it is of the inductee type with the same parameters
            // that were fixed earlier (indices may vary).
            par.ty.head().is_path_to(ind_def_path)
                && iter::zip(ind_def_params, par.ty.args())
                    .all(|(par, arg)| arg.is_var_with_id(par.id))
        })
        .map(|(i, _par)| i)
}

// TODO: simply copying the binding params over from the inductive definition is sure to cause
// subtle problems later down the line, but i'm tired so good luck future jacob
// TODO: look at redundancy in where this function constructs expressions; seems like it's making
// the same kinds of structures over and over
#[instrument(level = "trace", skip_all, fields(path = %ind_def_path))]
fn elim_ty(
    ind_def_path: Path,
    ind_def_params: &[BindingParam],
    ind_def_ty: &Expr,
    constructors: &[(Ident, Expr)],
) -> Expr {
    // Elim first fixes values of all parameters
    let mut res_params: Vec<BindingParam> = ind_def_params.iter().cloned().collect();

    // The type family that we are inducting in must take values of all indices...
    let mut family_params: Vec<BindingParam> =
        ind_def_ty.fn_ty_params().into_iter().cloned().collect();

    // ...and then an element of the inductive type itself...
    let family_last_param = BindingParam::blank(
        iter::chain(res_params.clone(), family_params.clone())
            .fold(Expr::path(ind_def_path.clone(), None), |acc, par| {
                Expr::fn_app(acc, par.to_var(), None)
            }),
    );
    family_params.push(family_last_param);

    // ...and return a Type.
    let family_ty = family_params
        .into_iter()
        .rfold(Expr::type_type(None), |acc, par| {
            Expr::fn_type(par, acc, None)
        });

    let family_param = BindingParam::new(Ident::from_str("family"), family_ty);

    res_params.push(family_param.clone());

    // Construct arm types
    for (constructor_name, constructor_ty) in constructors {
        let mut arm_params: Vec<BindingParam> =
            constructor_ty.fn_ty_params().into_iter().cloned().collect();

        // Append recursive parameters
        for i in recursible_param_idxs(&ind_def_path, ind_def_params, constructor_ty) {
            let arm_param = &arm_params[i];

            // To get the type of its resulting recursive parameter, apply the type family
            // to it, making sure to feed in the correct index values.
            let mut family_args: Vec<Expr> = arm_param
                .ty
                .args()
                .into_iter()
                .cloned()
                .skip(ind_def_params.len())
                .collect();

            family_args.push(arm_param.clone().to_var());

            let rec_par_ty = family_args
                .into_iter()
                .fold(family_param.clone().to_var(), |acc, arg| {
                    Expr::fn_app(acc, arg, None)
                });

            let rec_par_name = Ident::new(format!("{}_rec", arm_param.name.name));

            arm_params.push(BindingParam::new(rec_par_name, rec_par_ty));
        }

        // The codomain of an arm is the type family with indices corresponding to those in the
        // codomain of the corresponding constructor...
        let mut family_args: Vec<Expr> = constructor_ty
            .root_cod()
            .args()
            .into_iter()
            .cloned()
            .skip(ind_def_params.len())
            .collect();

        // ...and final argument being the application of the constructor to all of the arm's non-
        // recursive params.
        let mut constructor_path = ind_def_path.clone();
        constructor_path.components.push(constructor_name.clone());

        let constructor_args: Vec<Expr> =
            iter::chain(ind_def_params, constructor_ty.fn_ty_params())
                .cloned()
                .map(BindingParam::to_var)
                .collect();

        let family_last_arg = constructor_args
            .into_iter()
            .fold(Expr::path(constructor_path, None), |acc, arg| {
                Expr::fn_app(acc, arg, None)
            });

        family_args.push(family_last_arg);

        let arm_cod = family_args
            .into_iter()
            .fold(family_param.clone().to_var(), |acc, arg| {
                Expr::fn_app(acc, arg, None)
            });

        let arm_ty = arm_params
            .into_iter()
            .rfold(arm_cod, |acc, param| Expr::fn_type(param, acc, None));

        let arm_name = Ident::new(format!("{constructor_name}_case"));

        res_params.push(BindingParam::new(arm_name, arm_ty));
    }

    // Finally, `elim` takes a scrutinee, including the appropriate index parameters...
    let scrutinee_idx_params = ind_def_ty.fn_ty_params().into_iter().cloned();
    let scrutinee_final_param_ty = iter::chain(ind_def_params, ind_def_ty.fn_ty_params())
        .cloned()
        .map(BindingParam::to_var)
        .fold(Expr::path(ind_def_path, None), |acc, arg| {
            Expr::fn_app(acc, arg, None)
        });
    let scrutinee_final_param = BindingParam::blank(scrutinee_final_param_ty);

    res_params.extend(scrutinee_idx_params.clone());
    res_params.push(scrutinee_final_param.clone());

    // ...and returns the family applied to that scrutinee.
    let mut res_cod_args: Vec<Expr> = scrutinee_idx_params.map(BindingParam::to_var).collect();
    let res_cod_final_arg = scrutinee_final_param.to_var();
    res_cod_args.push(res_cod_final_arg);

    let res_cod = res_cod_args
        .into_iter()
        .fold(family_param.to_var(), |acc, arg| {
            Expr::fn_app(acc, arg, None)
        });

    // TODO: do I need to evaluate this before returning it?
    let res = res_params
        .into_iter()
        .rfold(res_cod, |acc, par| Expr::fn_type(par, acc, None));

    trace!("ret: {res}");

    res
}

impl Expr {
    #[instrument(level = "trace", skip(md, ctx), fields(self = %self, expected = %expected))]
    fn expect_ty(&self, expected: &Self, md: &Module, ctx: &Context) -> Result<()> {
        let mut expected = expected.clone();
        let expected_ty = expected.ty(md, ctx)?;

        if !Self::eq_up_to_vars(&expected_ty, &Self::type_type(None)) {
            bail!(
                expected.span(),
                "mismatched types: expected `Type`, found `{expected_ty}`"
            );
        }

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
            Path { path, span } => {
                if let Some(item) = md.items.get(path) {
                    item.ty()
                } else if let parent = path.clone().parent()
                    && let Some(Item::Inductive {
                        params,
                        ty,
                        constructors,
                    }) = md.items.get(&parent)
                {
                    let last_component = path.components.last().expect("paths are non-empty");

                    if last_component.name == "elim" {
                        elim_ty(parent, params, ty, constructors)
                    } else if let Some((_name, ty)) = constructors
                        .iter()
                        .find(|(name, _ty)| name == last_component)
                    {
                        params
                            .iter()
                            .cloned()
                            .rfold(ty.clone(), |acc, par| Expr::fn_type(par, acc, None))
                    } else {
                        bail!(span.clone(), "cannot find item `{path}` in this scope")
                    }
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

                let mut cod = body.ty(md, &ctx.clone().with_var(param.id, param.ty.clone()))?;

                let mut body = (**body).clone();
                let new_id = Uuid::new_v4();
                let new_var = Expr::Var {
                    id: new_id,
                    name: param.name.clone(),
                    span: None,
                };
                body.substitute(param.id, &new_var);
                cod.substitute(param.id, &new_var);

                FnType {
                    param: Rc::new(BindingParam {
                        id: new_id,
                        ..(**param).clone()
                    }),
                    cod: Rc::new(cod),
                    span: None,
                }
            }
            FnType { param, cod, .. } => {
                param.ty.expect_ty(&TypeType { span: None }, md, ctx)?;

                let ctx = ctx.clone().with_var(param.id, param.ty.clone());
                cod.expect_ty(&TypeType { span: None }, md, &ctx)?;

                TypeType { span: None }
            }
            FnApp { func, arg, .. } => {
                let mut func_type = func.ty(md, ctx)?;
                func_type.eval(md, ctx)?;

                let FnType { param, mut cod, .. } = func_type else {
                    bail!(func.span(), "expected function, found `{func_type}`");
                };

                arg.expect_ty(&param.ty, md, ctx)?;

                Rc::make_mut(&mut cod).substitute(param.id, arg);
                Rc::unwrap_or_clone(cod)
            }
        };

        trace!("return: {res}");

        Ok(res)
    }
}

fn expect_valid_inductive_def_ty(ty: &Expr) -> Result<()> {
    match ty {
        Expr::FnType { cod, .. } => expect_valid_inductive_def_ty(cod),
        Expr::TypeType { .. } => Ok(()),
        other => bail!(
            other.span(),
            "`{other}` is not a valid type for an inductive definition"
        ),
    }
}

impl Item {
    pub fn ty(&self) -> Expr {
        match self {
            Item::Def { ty, .. } | Item::Axiom { ty } => ty.clone(),
            Item::Inductive { params, ty, .. } => params
                .iter()
                .rfold(ty.clone(), |cod, par| Expr::fn_type(par.clone(), cod, None)),
        }
    }

    #[instrument(level = "trace", skip(self, md), fields(self = %self, path = %path))]
    pub fn type_check(&self, path: &Path, md: &Module) -> Result<()> {
        let last_component = path.components.last().expect("paths are non-empty");
        if last_component.name == "elim" {
            bail!(
                last_component.span.clone(),
                "`elim` is a reserved name in this position"
            );
        }

        match self {
            Item::Def { ty, val } => val.expect_ty(ty, md, &Context::Empty)?,
            Item::Axiom { ty } => ty.expect_ty(&Expr::type_type(None), md, &Context::Empty)?,
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

                ty.expect_ty(&Expr::TypeType { span: None }, md, &ctx)?;

                expect_valid_inductive_def_ty(ty)?;

                let ctx = Context::ThisInductive {
                    outer: Rc::new(ctx),
                    path: path.clone(),
                    ty: self.ty(),
                };

                for (_name, ty) in constructors {
                    ty.expect_ty(&Expr::TypeType { span: None }, md, &ctx)?;

                    if !ty.root_cod().head().is_path_to(path) {
                        bail!(
                            ty.root_cod().span(),
                            "Constructor for `{path}` does not return `{path}`"
                        );
                    }

                    // TODO: positivity checking
                }
            }
        }

        Ok(())
    }
}
