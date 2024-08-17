use std::rc::Rc;

use crate::{
    ast::{
        desugared::{Expr, Item, Module},
        Path,
    },
    err::Result,
    kernel::{context::Context, typeck::recursible_param_idxs},
};

use tracing::{instrument, trace};

use uuid::Uuid;

/// Check if the given expression is ready for eliminator-constructor simplification. If so, do it.
#[instrument(level = "trace", skip_all, fields(elim_call = %elim_call))]
fn try_eval_elim(elim_call: Expr, md: &Module, ctx: &Context) -> Option<Expr> {
    let Expr::Path {
        path: head_path, ..
    } = elim_call.head()
    else {
        return None;
    };

    if head_path.last_component().name != "elim" {
        return None;
    }

    let ind_def_path = head_path.clone().parent();

    let Some(Item::Inductive {
        params: ind_def_params,
        ty: ind_def_ty,
        constructors,
    }) = md.items.get(&ind_def_path)
    else {
        return None;
    };

    let elim_call_args = elim_call.args();

    if elim_call_args.len()
        != ind_def_params.len() + constructors.len() + ind_def_ty.fn_ty_params().len() + 2
    {
        trace!("potential elim-cons seems to be a subexpr of complete elim-cons; passing");
        return None;
    }

    let cons_call = elim_call_args.last()?;

    let Expr::Path {
        path: cons_path, ..
    } = cons_call.head()
    else {
        return None;
    };

    if cons_path.clone().parent() != ind_def_path {
        return None;
    }

    let Some(cons_idx) = constructors
        .iter()
        .position(|(name, _ty)| name == cons_path.last_component())
    else {
        return None;
    };

    trace!("potential elim-cons passed all guards; simplifying");

    let (_cons_name, cons_ty) = &constructors[cons_idx];

    let elim_args = elim_call.args();

    let matching_arm = elim_args
        .iter()
        .skip(ind_def_params.len() + 1)
        .nth(cons_idx)
        .expect("type-checked eliminator calls should have the right number of arguments");

    let mut arm_args: Vec<Expr> = cons_call
        .args()
        .iter()
        .skip(ind_def_params.len())
        .map(|&arg| arg.clone())
        .collect();

    for i in recursible_param_idxs(&ind_def_path, ind_def_params, cons_ty) {
        let mut rec_call_args: Vec<Expr> = elim_call.args().into_iter().cloned().collect();

        for _ in 0..(ind_def_ty.fn_ty_params().len() + 1) {
            rec_call_args.pop();
        }

        let recursible_arg = cons_call
            .args()
            .into_iter()
            .skip(ind_def_params.len())
            .nth(i)
            .expect("type-checked constructor calls should have the right number of arguments");

        let recursible_arg_ty = recursible_arg
            .ty(md, ctx)
            .expect("exprs should be type-checked before they are evaluated");

        let rec_call_idx_args = recursible_arg_ty
            .args()
            .into_iter()
            .skip(ind_def_params.len())
            .cloned();

        rec_call_args.extend(rec_call_idx_args);
        rec_call_args.push(recursible_arg.clone());

        let rec_call = rec_call_args
            .into_iter()
            .fold(elim_call.head().clone(), |acc, arg| {
                Expr::fn_app(acc, arg, None)
            });

        arm_args.push(rec_call);
    }

    let arm_call = arm_args
        .into_iter()
        .fold((*matching_arm).clone(), |acc, arg| {
            Expr::fn_app(acc, arg, None)
        });

    trace!("arm_call: {arm_call}");

    Some(arm_call)
}

impl Expr {
    pub fn substitute(&mut self, target_id: Uuid, sub: &Expr) {
        match self {
            Expr::TypeType { .. } => (),
            Expr::Var { id, .. } => {
                if *id == target_id {
                    *self = sub.clone()
                }
            }
            Expr::Path { .. } => (),
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.substitute(target_id, sub);
                Rc::make_mut(body).substitute(target_id, sub);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.substitute(target_id, sub);
                Rc::make_mut(cod).substitute(target_id, sub);
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).substitute(target_id, sub);
                Rc::make_mut(arg).substitute(target_id, sub);
            }
        }
    }

    pub fn contains_var(&self, search_id: Uuid) -> bool {
        match self {
            Expr::TypeType { .. } | Expr::Path { .. } => false,
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
        }
    }

    #[instrument(level = "trace", skip(self, md, ctx), fields(self = %self))]
    pub fn eval(&mut self, md: &Module, ctx: &Context) -> Result<()> {
        match self {
            Expr::TypeType { .. } => (),
            Expr::Var { .. } => (),
            Expr::Path { path, .. } => {
                if let Some(Item::Def { val, .. }) = md.items.get(path) {
                    *self = val.clone();
                }
            }
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.eval(md, ctx)?;
                Rc::make_mut(body).eval(md, ctx)?;

                // η-reduction: `[x] f x` reduces to `f` wherever `x` does not occur free in `f`.
                if let Expr::FnApp { func, arg, .. } = Rc::make_mut(body) {
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
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).eval(md, ctx)?;
                if let Expr::Fn { param, body, .. } = Rc::make_mut(func) {
                    Rc::make_mut(body).substitute(param.id, arg);
                    Rc::make_mut(body).eval(md, ctx)?;

                    *self = (**body).clone();
                } else {
                    Rc::make_mut(arg).eval(md, ctx)?;

                    if let Some(res) = try_eval_elim(self.clone(), md, ctx) {
                        *self = res;
                        self.eval(md, ctx)?;
                    }
                }
            }
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
                let mut param_ctx = Context::Empty;
                for param in params {
                    param.ty.eval(md, &param_ctx)?;
                    param_ctx = param_ctx.with_var(param.id, param.ty.clone());
                }

                ty.eval(md, &Context::Empty)?;

                for (_name, ty) in constructors {
                    ty.eval(md, &Context::Empty)?;
                }
            }
        }

        md.items.insert(path, self);

        Ok(())
    }
}
