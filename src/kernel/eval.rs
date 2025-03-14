use crate::log;

use std::{iter, rc::Rc};

use crate::{
    ast::desugared::{Expr, Item, Module},
    err::Result,
    kernel::{
        context::{Context, State},
        typeck::recursible_param_idxs,
    },
};

use super::context::MutState;

impl Expr {
    pub fn replace(&mut self, is_target: &impl Fn(&Expr) -> bool, sub: &Expr) {
        if is_target(self) {
            *self = sub.clone();
            return;
        }

        match self {
            Expr::TypeType { .. } | Expr::Rec { .. } | Expr::Var { .. } | Expr::Hole { .. } => (),
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
            Expr::Match { arg, cod_body, arms, .. } => {
                Rc::make_mut(arg).replace(is_target, sub);
                Rc::make_mut(cod_body).replace(is_target, sub);
                for arm in arms {
                    arm.body.replace(is_target, sub);
                }
            }
        }
    }

    pub fn substitute(&mut self, target_id: u128, sub: &Expr) {
        self.replace(&|expr| expr.is_var_with_id(target_id), sub)
    }

    pub fn with_substitution(mut self, target_id: u128, expr: Expr) -> Self {
        self.substitute(target_id, &expr);
        self
    }

    pub fn with_substitutions(
        mut self,
        target_ids: impl IntoIterator<Item = u128>,
        subs: impl IntoIterator<Item = Expr>,
    ) -> Self {
        for (target_id, sub) in iter::zip(target_ids, subs) {
            self.substitute(target_id, &sub);
        }
        self
    }

    // TODO: replace this with a more general method like `any_subexpr`
    pub fn contains_var(&self, search_id: u128) -> bool {
        match self {
            Expr::TypeType { .. } | Expr::Path { .. } | Expr::Rec { .. } | Expr::Hole { .. } => {
                false
            }
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
            Expr::Match { arg, cod_body, arms, .. } => {
                arg.contains_var(search_id)
                    || cod_body.contains_var(search_id)
                    || arms.iter().any(|arm| arm.body.contains_var(search_id))
            }
        }
    }

    pub fn eval(&mut self, state: State, mut_state: &mut MutState) -> Result<()> {
        let _guard = log::enter();
        log!("eval: {self}");

        match self {
            Expr::TypeType { .. } => (),
            Expr::Hole { .. } => {
                let val = mut_state.resolve_hole(self);
                // `value` is guaranteed to be in normal form because we only ever insert these
                // values from inside of `syn_eq_impl` which operates on normal exprs
                *self = val.clone();
            }
            Expr::Var { .. } => (),
            Expr::Path { path, .. } => {
                if let Some(Item::Def { val, .. }) = state.md.items.get(path) {
                    *self = val.clone();
                }
            }
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.eval(state.deeper(), mut_state)?;
                let new_ctx = state.ctx.clone().with_var(param.id, param.ty.clone());
                Rc::make_mut(body).eval(state.deeper().with_ctx(&new_ctx), mut_state)?;

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
                Rc::make_mut(param).ty.eval(state.deeper(), mut_state)?;
                let new_ctx = state.ctx.clone().with_var(param.id, param.ty.clone());
                Rc::make_mut(cod).eval(state.deeper().with_ctx(&new_ctx), mut_state)?;
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).eval(state.deeper(), mut_state)?;
                if let Expr::Fn { param, body, .. } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(param.id, arg);
                    Rc::make_mut(body).eval(state.deeper(), mut_state)?;

                    *self = (**body).clone();
                } else {
                    Rc::make_mut(arg).eval(state.deeper(), mut_state)?;
                }
            }
            Expr::Match { arg, arms, .. } => {
                let mut evald_arg = (**arg).clone();
                evald_arg.eval(state.deeper(), mut_state)?;

                let Expr::Path { path: cons_path, .. } = evald_arg.head() else {
                    *arg = Rc::new(evald_arg);
                    for arm in arms {
                        let new_ctx = state
                            .ctx
                            .clone()
                            .with_rec_vals(arm.cons_args.iter().map(|(_name, id)| (*id, None)));
                        arm.body.eval(state.deeper().with_ctx(&new_ctx), mut_state)?;
                    }
                    return Ok(());
                };

                let ind_def_path = cons_path.clone().parent();
                let cons_name = cons_path.last_component();

                let Some(Item::Inductive {
                    params: ind_def_params,
                    constructors: ind_def_constructors,
                    ..
                }) = state.md.items.get(&ind_def_path)
                else {
                    return Ok(());
                };

                let ind_def_num_params = ind_def_params.len();

                let Some((_name, cons_ty)) =
                    ind_def_constructors.iter().find(|(name, _ty)| name == cons_name)
                else {
                    return Ok(());
                };

                let Some(matching_arm) =
                    arms.iter().find(|arm| arm.constructor == *cons_name).cloned()
                else {
                    return Ok(());
                };

                let mut res = matching_arm.body.clone().with_substitutions(
                    matching_arm.cons_args.iter().map(|(_name, id)| *id),
                    evald_arg.args().into_iter().skip(ind_def_num_params).cloned(),
                );

                let mut res_ctx = state.ctx.clone();

                for i in recursible_param_idxs(&ind_def_path, &ind_def_params, cons_ty) {
                    let rec_cons_arg_id = matching_arm.cons_args[i].1;

                    let rec_call_arg = evald_arg.args()[i + ind_def_num_params].clone();

                    let mut rec_val = self.clone();

                    let Self::Match { arg, .. } = &mut rec_val else {
                        unreachable!();
                    };
                    *arg = Rc::new(rec_call_arg);

                    res_ctx = res_ctx.clone().with_rec_val(rec_cons_arg_id, Some(rec_val));
                }

                res.eval(state.deeper().with_ctx(&res_ctx), mut_state)?;

                *self = res;
            }
            Expr::Rec { arg_id, .. } => {
                if let Some(mut rec_val) = state.ctx.val_of_rec(*arg_id).cloned() {
                    rec_val.eval(state.deeper(), mut_state)?;
                    *self = rec_val;
                }
            }
        }

        log!("-> {self}");

        Ok(())
    }
}

impl Item {
    pub fn eval(&mut self, md: &mut Module, mut_state: &mut MutState) -> Result<()> {
        log!("eval: {self}");

        let state = State { md, ctx: &Context::Empty, depth: 0 };

        match self {
            Item::Def { ty, val, .. } => {
                ty.eval(state, mut_state)?;
                val.eval(state, mut_state)?;
            }
            Item::Axiom { ty, .. } => ty.eval(state, mut_state)?,
            Item::Inductive { params, ty, constructors, .. } => {
                let mut param_ctx = Context::Empty;
                for param in params {
                    param.ty.eval(state.with_ctx(&param_ctx), mut_state)?;
                    param_ctx = param_ctx.with_var(param.id, param.ty.clone());
                }

                ty.eval(state.with_ctx(&param_ctx), mut_state)?;

                for (_name, ty) in constructors {
                    ty.eval(state.with_ctx(&param_ctx), mut_state)?;
                }
            }
        }

        Ok(())
    }
}
