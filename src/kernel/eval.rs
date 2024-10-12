use std::{iter, rc::Rc};

use crate::{
    ast::desugared::{Expr, Item, Module},
    bail,
    err::Result,
    kernel::{context::Context, typeck::recursible_param_idxs},
};

use ulid::Ulid;

impl Expr {
    pub fn replace(&mut self, is_target: &impl Fn(&Expr) -> bool, sub: &Expr) {
        if is_target(self) {
            *self = sub.clone();
        }

        match self {
            Expr::TypeType { .. } | Expr::Rec { .. } | Expr::Var { .. } => (),
            Expr::Path { .. } => (),
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.replace(is_target, sub);
                Rc::make_mut(body).replace(is_target, sub);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.replace(is_target, sub);
                Rc::make_mut(cod).replace(is_target, sub);
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).replace(is_target, sub);
                Rc::make_mut(arg).replace(is_target, sub);
            }
            Expr::Match {
                arg,
                cod_body,
                arms,
                ..
            } => {
                Rc::make_mut(arg).replace(is_target, sub);
                Rc::make_mut(cod_body).replace(is_target, sub);
                for arm in arms {
                    arm.body.replace(is_target, sub);
                }
            }
        }
    }

    pub fn substitute(&mut self, target_id: Ulid, sub: &Expr) {
        self.replace(&|expr| expr.is_var_with_id(target_id), sub)
    }

    pub fn substitute_many<'a>(
        &mut self,
        target_ids: impl IntoIterator<Item = Ulid>,
        subs: impl IntoIterator<Item = &'a Expr>,
    ) {
        for (target_id, sub) in iter::zip(target_ids, subs) {
            self.substitute(target_id, sub);
        }
    }

    pub fn with_substitution(mut self, target_id: Ulid, expr: Expr) -> Self {
        self.substitute(target_id, &expr);
        self
    }

    pub fn with_substitutions(
        mut self,
        target_ids: impl IntoIterator<Item = Ulid>,
        subs: impl IntoIterator<Item = Expr>,
    ) -> Self {
        for (target_id, sub) in iter::zip(target_ids, subs) {
            self.substitute(target_id, &sub);
        }
        self
    }

    pub fn with_replacements<'a>(
        mut self,
        targets: impl IntoIterator<Item = &'a dyn Fn(&Self) -> bool>,
        subs: impl IntoIterator<Item = Expr>,
    ) -> Self {
        for (target, sub) in iter::zip(targets, subs) {
            self.replace(&target, &sub);
        }
        self
    }

    // TODO: replace this with a more general method like `any_subexpr`
    pub fn contains_var(&self, search_id: Ulid) -> bool {
        match self {
            Expr::TypeType { .. } | Expr::Path { .. } | Expr::Rec { .. } => false,
            Expr::Var { id, .. } => *id == search_id,
            Expr::Fn { param, body, .. } => {
                param.ty.contains_var(search_id) || body.contains_var(search_id)
            }
            Expr::FnType { param, cod, .. } => {
                param.ty.contains_var(search_id) || cod.contains_var(search_id)
            }
            Expr::FnApp { func, arg, .. } => {
                func.contains_var(search_id) || arg.contains_var(search_id)
            }
            Expr::Match {
                arg,
                cod_body,
                arms,
                ..
            } => {
                arg.contains_var(search_id)
                    || cod_body.contains_var(search_id)
                    || arms.iter().any(|arm| arm.body.contains_var(search_id))
            }
        }
    }

    pub fn eval(&mut self, md: &Module, ctx: &Context, depth: usize) -> Result<()> {
        println!("{blank:|>align$}eval: {self}", blank = "", align = depth);

        match self {
            Expr::TypeType { .. } => (),
            Expr::Var { .. } => (),
            Expr::Path { path, .. } => {
                if let Some(Item::Def { val, .. }) = md.items.get(path) {
                    *self = val.clone();
                }
            }
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.eval(md, ctx, depth + 1)?;
                Rc::make_mut(body).eval(
                    md,
                    &ctx.clone().with_var(param.id, param.ty.clone()),
                    depth + 1,
                )?;

                // η-reduction: `[x] f x` reduces to `f` wherever `x` does not occur free in `f`.
                if let Expr::FnApp { func, arg, .. } = Rc::make_mut(body)
                    && let Expr::Var { id: arg_id, .. } = **arg
                    && arg_id == param.id
                    && !func.contains_var(param.id)
                {
                    *self = (**func).clone();
                }
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.eval(md, ctx, depth + 1)?;
                Rc::make_mut(cod).eval(
                    md,
                    &ctx.clone().with_var(param.id, param.ty.clone()),
                    depth + 1,
                )?;
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).eval(md, ctx, depth + 1)?;
                if let Expr::Fn { param, body, .. } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(param.id, arg);
                    Rc::make_mut(body).eval(md, ctx, depth + 1)?;

                    *self = (**body).clone();
                } else {
                    Rc::make_mut(arg).eval(md, ctx, depth + 1)?;
                }
            }
            Expr::Match {
                ref arg, ref arms, ..
            } => {
                let mut evald_arg: Expr = (**arg).clone();
                evald_arg.eval(md, ctx, depth + 1)?;

                let Expr::Path {
                    path: cons_path, ..
                } = evald_arg.head()
                else {
                    return Ok(());
                };

                let ind_def_path = cons_path.clone().parent();
                let cons_name = cons_path.last_component();

                let Some(Item::Inductive {
                    params: ind_def_params,
                    constructors: ind_def_constructors,
                    ..
                }) = md.items.get(&ind_def_path)
                else {
                    return Ok(());
                };

                let ind_def_num_params = ind_def_params.len();

                let Some((_name, cons_ty)) = ind_def_constructors
                    .iter()
                    .find(|(name, _ty)| name == cons_name)
                else {
                    return Ok(());
                };

                let Some(matching_arm) = arms.iter().find(|arm| &arm.constructor == cons_name)
                else {
                    return Ok(());
                };

                let mut res = matching_arm.body.clone().with_substitutions(
                    matching_arm.cons_args.iter().map(|(_name, id)| *id),
                    evald_arg
                        .args()
                        .into_iter()
                        .skip(ind_def_num_params)
                        .cloned(),
                );

                let mut res_ctx = ctx.clone();

                for i in recursible_param_idxs(&ind_def_path, ind_def_params, cons_ty) {
                    let (_name, rec_cons_arg_id) = &matching_arm.cons_args[i];

                    let rec_call_arg = evald_arg.args()[i + ind_def_num_params].clone();

                    let mut rec_val = self.clone();

                    let Self::Match { arg, .. } = &mut rec_val else {
                        unreachable!();
                    };
                    *arg = Rc::new(rec_call_arg);

                    res_ctx = res_ctx.clone().with_rec_val(*rec_cons_arg_id, rec_val);
                }

                res.eval(md, &res_ctx, depth + 1)?;

                *self = res;
            }
            Expr::Rec { arg_id, .. } => {
                if let Some(mut rec_val) = ctx.val_of_rec(*arg_id).cloned() {
                    rec_val.eval(md, ctx, depth + 1)?;
                    *self = rec_val;
                }
            }
        }

        println!("{blank:|>depth$}|-> {self}", blank = "");

        Ok(())
    }
}

impl Item {
    pub fn eval(&mut self, md: &mut Module) -> Result<()> {
        println!("eval: {self}");

        match self {
            Item::Def { ty, val, .. } => {
                ty.eval(md, &Context::Empty, 0)?;
                val.eval(md, &Context::Empty, 0)?;
            }
            Item::Axiom { ty, .. } => ty.eval(md, &Context::Empty, 0)?,
            Item::Inductive {
                params,
                ty,
                constructors,
                ..
            } => {
                let mut param_ctx = Context::Empty;
                for param in params {
                    param.ty.eval(md, &param_ctx, 0)?;
                    param_ctx = param_ctx.with_var(param.id, param.ty.clone());
                }

                ty.eval(md, &Context::Empty, 0)?;

                for (_name, ty) in constructors {
                    ty.eval(md, &Context::Empty, 0)?;
                }
            }
        }

        Ok(())
    }
}
