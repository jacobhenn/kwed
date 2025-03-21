use yansi::Paint;

use crate::{
    ast::{
        desugared::{id_color, Arm, BindingParam, Expr, Item, Module},
        Ident, Path, Span,
    },
    bail,
    err::Result,
    kernel::context::{Context, MutState, State},
    log,
};

use std::{cmp, iter, rc::Rc};

// TODO: possibly replace this with `recursible_params` to be more idiomatic
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

fn match_ty(
    arg: &Expr,
    cod_pars: &[(Ident, u128)],
    cod_body: &Expr,
    arms: &[Arm],
    match_span: &Option<Span>,
    state: State,
    mut_state: &mut MutState,
) -> Result<Expr> {
    // The internal documentation of this function will use the example of an inductively-defined
    // type of lists of given length, called `Vec`. The definition in `kwed` syntax is as follows:
    // ```kwed
    // inductive Vec(A: Type): ℕ → Type {
    // 	   nil: Vec A ℕ.0,
    // 	   cons: (n: ℕ, Vec A n, A) → Vec A (ℕ.suc n),
    // }
    // ```
    //
    // Furthermore, the example match statement that we will be type-checking is the body of this
    // function:
    // ```kwed
    // match v to [n v] Vec A (ℕ.suc n) {
    // 	   nil => Vec.cons A ℕ.0 (Vec.nil A) a,
    // 	   cons n' v' a' => Vec.cons A (ℕ.suc n') (rec v') a',
    // }
    // ```

    // the type of the scrutinee: `Vec A n`
    let mut arg_ty = arg.ty(state.deeper(), mut_state)?;
    // evaluated so that we can match on type aliases
    arg_ty.eval(state.deeper(), mut_state)?;

    let ind_ty = arg_ty.head();

    // the head of the scrutinee type; e.g. the type we are inducting over: `Vec`
    let Expr::Path { path: ind_def_path, level: arg_level, .. } = ind_ty else {
        bail!(
            arg.span(), "cannot match on non-inductive type `{}`", arg_ty.head();
            arg_ty.head().span(), "defined here"
        );
    };

    // ind_def_params: `(A: Type)`
    // ind_def_ty: `ℕ → Type`
    // ind_def_constructors:
    // ```
    // nil: Vec A ℕ.0,
    // cons: (n: ℕ, Vec A n, A) → Vec A (ℕ.suc n),
    // ```
    let Some(Item::Inductive {
        params: ind_def_params,
        ty: ind_def_ty,
        constructors: ind_def_constructors,
    }) = state.md.items.get(ind_def_path)
    else {
        bail!(arg.span(), "cannot match on `{}` - not in scope or not inductive", ind_ty);
    };

    let mut ind_def_params = ind_def_params.clone();
    let mut ind_def_ty = ind_def_ty.clone();
    let mut ind_def_constructors = ind_def_constructors.clone();

    for param in &mut ind_def_params {
        param.ty.displace(*arg_level);
    }
    ind_def_ty.displace(*arg_level);
    for (_name, ty) in &mut ind_def_constructors {
        ty.displace(*arg_level);
    }

    // the indices specified in the type of the inductive definition: `(●: ℕ)`
    let ind_def_indices = ind_def_ty.fn_ty_params().into_iter();

    // the number of parameters specified in the inductive definition: 1
    let ind_def_num_params = ind_def_params.len();
    // the number of indices specified in the inductive definition: 1
    let ind_def_num_indices = ind_def_indices.len();

    // the UUIDs of the parameters to the codomain: `[n v]`
    let cod_par_ids = cod_pars.iter().map(|(_cod_par_name, cod_par_id)| *cod_par_id);

    // the particular parameter values of the inductive type that we will be matching over. unlike
    // indices, parameters cannot change over the course of an induction. `A`
    let arg_par_vals = arg_ty.args().into_iter().take(ind_def_num_params);

    // the particular index values of the scrutinee. `n`
    let arg_idx_vals = arg_ty.args().into_iter().skip(ind_def_num_params);

    if cod_pars.len() != ind_def_num_indices + 1 {
        bail!(
            match_span.clone(),
            "incorrect number of parameters in the codomain: expected {}, found {}",
            ind_def_num_indices + 1,
            cod_pars.len()
        );
    }

    let (_cod_final_par_name, cod_final_par_id) =
        cod_pars.last().expect("codomain should have at least one parameter");

    // -- type-check the codomain

    // the types of the index parameters of the codomain, obtained from the index types specified
    // in the inductive definition. `(ℕ)`
    let cod_idx_par_tys = ind_def_indices.clone().map(|par| {
        par.ty.clone().with_substitutions(
            ind_def_params.iter().map(|par| par.id),
            arg_par_vals.clone().cloned(),
        )
    });

    // the type of the final parameter of the codomain, obtained from applying the inductive type
    // former first to the fixed parameter values and second to the particular index values of
    // the scrutinee. `Vec A n`
    let cod_final_par_ty = ind_ty
        .clone()
        .with_args(arg_par_vals.clone().cloned())
        .with_args(ind_def_indices.clone().cloned().map(BindingParam::to_var));

    // the context in which to type-check the codomain: `{n: ℕ, v: Vec A n}`
    let cod_ctx = state
        .ctx
        .clone()
        .with_vars(cod_par_ids.clone().zip(cod_idx_par_tys))
        .with_var(*cod_final_par_id, cod_final_par_ty);

    // TODO: do I need to do something with this level?
    cod_body.expect_ty_ty(state.deeper().with_ctx(&cod_ctx), mut_state)?;

    // -- check exhaustivity

    for (cons_name, _) in &ind_def_constructors {
        if !arms.iter().any(|arm| arm.constructor == *cons_name) {
            bail!(
                match_span.clone(),
                "non-exhaustive match: missing constructor `{cons_name}`";
                cons_name.span.clone(), "defined here"
            )
        }
    }

    for (i, arm) in arms.iter().enumerate() {
        if let Some((_, dup_arm)) = arms
            .iter()
            .enumerate()
            .find(|(j, other_arm)| other_arm.constructor == arm.constructor && i != *j)
        {
            bail!(
                arm.constructor.span.clone(), "constructor `{}` is matched twice", arm.constructor;
                dup_arm.constructor.span.clone(), "duplicate"
            )
        }
    }

    // -- type-check the arms

    for arm in arms {
        // the arm used in this example will be the second one, namely
        // ```kwed
        // 	   cons n' v' a' => Vec.cons A (ℕ.suc n') (rec v') a',
        // ```

        // arm.constructor: Ident: the constructor that we are matching for: `cons`
        // arm.cons_args: Vec<(Ident, u128)>: the arguments of the constructor we are binding:
        //     `n' v' a'`
        // arm.body: Expr: the return value of the arm: `Vec.cons A (ℕ.suc n') (rec v') a'`

        // cons_ty: the type of the constructor for this arm: `(n: ℕ, Vec A n, A) → Vec A (ℕ.suc n)`
        let Some((_, cons_ty)) =
            ind_def_constructors.iter().find(|(cons_name, _)| cons_name == &arm.constructor)
        else {
            bail!(
                arm.constructor.span.clone(), "no such constructor `{}`", arm.constructor;
                arg_ty.span().clone(), "inductive type defined here"
            )
        };

        // cons_pars: the parameters of the constructor in question: `(n: ℕ, Vec A n, A)`
        let cons_pars: Vec<BindingParam> = cons_ty.fn_ty_params().into_iter().cloned().collect();

        if arm.cons_args.len() != cons_pars.len() {
            bail!(
                arm.constructor.span.clone(),
                "wrong number of arguments to `{}`: expected {}, found {}",
                arm.constructor,
                cons_pars.len(),
                arm.cons_args.len();
                cons_ty.span().clone(),
                "defined here"
            );
        }

        let cons_arg_ids = arm.cons_args.iter().map(|(_cons_arg_name, cons_arg_id)| *cons_arg_id);

        // the types of the arguments to the constructor of this arm, obtained by taking the
        // parameters of the constructor and substituting in the appropriate values for the
        // inductive type parameters and previously bound paramaters: `(ℕ, Vec A n', A)`
        let cons_arg_tys = cons_pars.iter().map(|par| {
            par.ty
                .clone()
                .with_substitutions(
                    ind_def_params.iter().map(|par| par.id),
                    arg_par_vals.clone().cloned(),
                )
                .with_substitutions(
                    cons_pars.iter().map(|par| par.id),
                    arm.cons_args.iter().map(|(name, id)| Expr::var(*id, name.clone())),
                )
        });

        // the context in which to type-check the body of this arm. initially, this context is
        //     `{n': ℕ, v': Vec A n', a': A}`
        let mut arm_ctx = state.ctx.clone().with_vars(
            cons_arg_ids
                .clone()
                .zip(cons_arg_tys.clone())
                .map(|(cons_arg_id, cons_arg_ty)| (cons_arg_id, cons_arg_ty)),
        );

        // add recursible parameters to the arm context
        for i in recursible_param_idxs(&ind_def_path, &ind_def_params, &cons_ty) {
            let (rec_cons_arg_name, rec_cons_arg_id) = &arm.cons_args[i];

            let rec_par_ty = cons_arg_tys.clone().nth(i).expect("recursible_param_idxs is correct");

            // indices to pass to the codomain to get the type of the recursive application of
            // this match-expression to the recursible parameter: `n`
            let cod_idx_args = rec_par_ty.args().into_iter().skip(ind_def_params.len());

            // the type of the recursive application of this match-expression to the recursible
            // parameter: `Vec A (ℕ.suc n')`
            let rec_call_ty = cod_body
                .clone()
                .with_substitutions(cod_par_ids.clone(), cod_idx_args.cloned())
                .with_substitution(
                    *cod_final_par_id,
                    Expr::var(*rec_cons_arg_id, rec_cons_arg_name.clone()),
                );

            arm_ctx = arm_ctx.with_rec_ty(*rec_cons_arg_id, rec_call_ty);
        }

        // the elaborated version of the scrutinee given that in this branch we know it to have
        // come from `arm.constructor` (`Vec.cons`): `Vec.cons n' v' a'`
        let cod_final_arg = ind_def_path
            .clone()
            .with_suffix(arm.constructor.clone())
            .to_expr(*arg_level)
            .with_args(arg_par_vals.clone().cloned())
            .with_args(arm.cons_args.iter().map(|(name, id)| Expr::var(*id, name.clone())));

        // the elaborated type of the scrutinee given that in this branch we know some of its
        // indices to have been constructed from indices of a lower structural component:
        //     `Vec A (ℕ.suc n')`
        let cod_final_arg_ty = cod_final_arg.ty(state.deeper().with_ctx(&arm_ctx), mut_state)?;

        // the elaborated indices of the scrutinee: `(ℕ.suc n')`
        let cod_idx_args = cod_final_arg_ty.args().into_iter().skip(ind_def_num_params);

        // the expected type of the body of this arm, obtained from applying the type family towards
        // which we are inducting to the elaborated version of the scrutinee:
        //     `Vec A (ℕ.suc (ℕ.suc n'))`
        let arm_expected_ty = cod_body
            .clone()
            .with_substitutions(cod_par_ids.clone(), cod_idx_args.cloned())
            .with_substitution(*cod_final_par_id, cod_final_arg);

        arm.body.expect_ty(&arm_expected_ty, state.deeper().with_ctx(&arm_ctx), mut_state)?;
    }

    // the resulting type of the entire match expression, obtained by applying the type family
    // towards which we are matching to the scrutinee: `Vec A (ℕ.suc n)`
    let res = cod_body
        .clone()
        .with_substitutions(cod_par_ids, arg_idx_vals.cloned())
        .with_substitution(*cod_final_par_id, arg.clone());

    Ok(res)
}

#[derive(Clone, Debug)]
enum SynEqCtx {
    Empty,
    Pair(Box<Self>, [u128; 2]),
}

impl SynEqCtx {
    fn with_pair(self, pair: [u128; 2]) -> Self {
        Self::Pair(Box::new(self), pair)
    }

    fn with_pairs(self, pairs: impl IntoIterator<Item = [u128; 2]>) -> Self {
        pairs.into_iter().fold(self, |acc, pair| acc.with_pair(pair))
    }

    fn contains_pair(&self, search_pair: [u128; 2]) -> bool {
        match self {
            SynEqCtx::Empty => false,
            SynEqCtx::Pair(outer, pair) => *pair == search_pair || outer.contains_pair(search_pair),
        }
    }
}

impl Expr {
    fn hole_syn_eq(hole_id: u128, rhs: &Self, state: &mut MutState) -> bool {
        // TODO: figure out how this interacts with free variables
        log!("filling hole {} with {rhs}", "_".paint(id_color(hole_id).background()));
        state.hole_vals.insert(hole_id, rhs.clone());
        true
    }

    fn syn_eq_impl(lhs: &Self, rhs: &Self, ctx: &SynEqCtx, state: &mut MutState) -> bool {
        match (lhs, rhs) {
            (Expr::Hole { id, .. }, rhs) => Self::hole_syn_eq(*id, rhs, state),
            (lhs, Expr::Hole { id, .. }) => Self::hole_syn_eq(*id, lhs, state),
            (Expr::TypeType { level: ll, .. }, Expr::TypeType { level: rl, .. }) => ll == rl,
            (Expr::Var { id: lid, .. }, Expr::Var { id: rid, .. })
            | (Expr::Rec { arg_id: lid, .. }, Expr::Rec { arg_id: rid, .. }) => {
                lid == rid || ctx.contains_pair([*lid, *rid])
            }
            (Expr::Path { path: lpath, .. }, Expr::Path { path: rpath, .. }) => lpath == rpath,
            (
                Expr::Fn { param: lparam, body: lbody, .. },
                Expr::Fn { param: rparam, body: rbody, .. },
            ) => {
                if !Self::syn_eq_impl(&lparam.ty, &rparam.ty, ctx, state) {
                    return false;
                }

                let body_ctx = ctx.clone().with_pair([lparam.id, rparam.id]);
                Self::syn_eq_impl(lbody, rbody, &body_ctx, state)
            }
            (
                Expr::FnType { param: lparam, cod: lcod, .. },
                Expr::FnType { param: rparam, cod: rcod, .. },
            ) => {
                if !Self::syn_eq_impl(&lparam.ty, &rparam.ty, ctx, state) {
                    return false;
                }

                let cod_ctx = ctx.clone().with_pair([lparam.id, rparam.id]);
                Self::syn_eq_impl(lcod, rcod, &cod_ctx, state)
            }
            (
                Expr::FnApp { func: lfunc, arg: larg, .. },
                Expr::FnApp { func: rfunc, arg: rarg, .. },
            ) => {
                Self::syn_eq_impl(lfunc, rfunc, ctx, state)
                    && Self::syn_eq_impl(larg, rarg, ctx, state)
            }

            (
                Expr::Match {
                    arg: larg,
                    cod_pars: lcod_pars,
                    cod_body: lcod_body,
                    arms: larms,
                    ..
                },
                Expr::Match {
                    arg: rarg,
                    cod_pars: rcod_pars,
                    cod_body: rcod_body,
                    arms: rarms,
                    ..
                },
            ) => {
                if !Self::syn_eq_impl(larg, rarg, ctx, state) {
                    return false;
                }

                let cod_body_ctx = ctx.clone().with_pairs(
                    iter::zip(lcod_pars, rcod_pars).map(|((_, lid), (_, rid))| [*lid, *rid]),
                );

                if !Self::syn_eq_impl(lcod_body, rcod_body, &cod_body_ctx, state) {
                    return false;
                }

                for (larm, rarm) in iter::zip(larms, rarms) {
                    let arm_body_ctx = ctx.clone().with_pairs(
                        iter::zip(&larm.cons_args, &rarm.cons_args)
                            .map(|((_, lid), (_, rid))| [*lid, *rid]),
                    );

                    if !Self::syn_eq_impl(&larm.body, &rarm.body, &arm_body_ctx, state) {
                        return false;
                    }
                }

                true
            }
            (_, _) => false,
        }
    }

    pub fn syn_eq(lhs: &Self, rhs: &Self, state: &mut MutState) -> bool {
        Self::syn_eq_impl(lhs, rhs, &SynEqCtx::Empty, state)
    }

    fn expect_ty(&self, expected: &Self, state: State, mut_state: &mut MutState) -> Result<()> {
        let expected_ty = expected.ty(state.deeper(), mut_state)?;
        if !expected_ty.is_type_type() {
            if expected.span().is_none() {
                log!("expectation failed on spanless ty `{self}`");
            }

            bail!(expected.span(), "expected type, found `{expected_ty}`");
        }

        let mut expected_evald = expected.clone();
        expected_evald.eval(state.deeper(), mut_state)?;

        let found = self.ty(state.deeper(), mut_state)?;
        let mut found_evald = found.clone();
        found_evald.eval(state.deeper(), mut_state)?;

        if let Expr::TypeType { level: found_level, .. } = found_evald
            && let Expr::TypeType { level: expected_level, .. } = expected_evald
            && found_level <= expected_level
        {
            return Ok(());
        } else if Self::syn_eq(&found_evald, &expected_evald, mut_state) {
            return Ok(());
        }

        if self.span().is_none() {
            log!("expectation failed on spanless expr `{self}`");
        }

        bail!(
            self.span(),
            "mismatched types:\n    expected `{expected}`,\n    found    `{found}`";
            expected_evald.span(),
            "expected this";
            @note "evaluated:";
            @note "  expected `{expected_evald}`";
            @note "  found    `{found_evald}`"
        )
    }

    fn expect_ty_ty(&self, state: State, mut_state: &mut MutState) -> Result<usize> {
        let mut found = self.ty(state.deeper(), mut_state)?;
        found.eval(state.deeper(), mut_state)?;

        match found {
            Expr::TypeType { level, .. } => Ok(level),
            other => bail!(self.span(), "expected type, found `{other}`"),
        }
    }

    // TODO: verify assumption that this returns exprs in normal form
    pub fn ty(&self, state: State, mut_state: &mut MutState) -> Result<Self> {
        let _guard = log::enter();
        log!("ty: {self}");

        let res = match self {
            Self::TypeType { level, .. } => Self::TypeType { level: level + 1, span: None },
            Self::Hole { id, span } => {
                mut_state.all_holes.insert((*id, *span));
                if let Some(ty) = mut_state.hole_tys.get(id) {
                    mut_state.resolve_hole(ty).clone()
                } else {
                    let new_id = fastrand::u128(..);
                    let new_ty = Self::Hole { id: new_id, span: None };
                    mut_state.hole_tys.insert(*id, new_ty.clone());
                    mut_state.all_holes.insert((new_id, None));
                    new_ty
                }
            }
            Self::Var { id, .. } => {
                let Some(ty) = state.ctx.ty_of_var(*id) else {
                    panic!("unbound variable. ctx: {}", state.ctx);
                };
                ty.clone()
            }
            Self::Path { path, span, level } => {
                let mut res = if let Some(item) = state.md.items.get(path)
                    && let Some(ty) = item.ty()
                {
                    ty
                } else if let parent = path.clone().parent()
                    && let Some(Item::Inductive { params, constructors, .. }) =
                        state.md.items.get(&parent)
                    && let Some(last_component) = path.components.last()
                    && let Some((_name, ty)) =
                        constructors.iter().find(|(name, _ty)| name == last_component)
                {
                    ty.clone().with_fn_ty_params(params.iter().cloned())
                } else if let Some((ind_path, ty)) = state.ctx.this_inductive()
                    && path == ind_path
                {
                    ty.clone()
                } else {
                    bail!(span.clone(), "cannot find item `{path}` in this scope")
                };

                res.displace(*level);
                res
            }
            // TODO: clean this up
            Self::Fn { param, body, .. } => {
                param.ty.expect_ty_ty(state.deeper(), mut_state)?;

                let new_ctx = state.ctx.clone().with_var(param.id, param.ty.clone());
                let mut cod = body.ty(state.deeper().with_ctx(&new_ctx), mut_state)?;

                let mut body = (**body).clone();
                let new_id = fastrand::u128(..);
                let new_var = (**param).clone().with_id(new_id).to_var();
                body.substitute(param.id, &new_var);
                cod.substitute(param.id, &new_var);

                Self::FnType {
                    param: Rc::new(BindingParam { id: new_id, ..(**param).clone() }),
                    cod: Rc::new(cod),
                    span: None,
                }
            }
            Self::FnType { param, cod, .. } => {
                let param_level = param.ty.expect_ty_ty(state.deeper(), mut_state)?;

                let new_ctx = state.ctx.clone().with_var(param.id, param.ty.clone());
                let cod_level = cod.expect_ty_ty(state.deeper().with_ctx(&new_ctx), mut_state)?;

                Self::TypeType { level: cmp::max(param_level, cod_level), span: None }
            }
            Self::FnApp { func, arg, .. } => {
                let mut func_type = func.ty(state.deeper(), mut_state)?;
                func_type.eval(state.deeper(), mut_state)?;

                let Self::FnType { param, mut cod, .. } = func_type else {
                    bail!(
                        func.span(), "expected function, found `{func_type}`";
                        arg.span(), "non-function expression is applied to this argument"
                    );
                };

                arg.expect_ty(&param.ty, state.deeper(), mut_state)?;

                Rc::make_mut(&mut cod).substitute(param.id, arg);
                Rc::unwrap_or_clone(cod)
            }
            Expr::Match { arg, cod_pars, cod_body, arms, span } => {
                match_ty(arg, cod_pars, cod_body, arms, span, state.deeper(), mut_state)?
            }
            Expr::Rec { arg_name, arg_id, .. } => {
                if let Some(ty_of_rec) = state.ctx.ty_of_rec(*arg_id) {
                    ty_of_rec.clone()
                } else if state.ctx.ty_of_var(*arg_id).is_some() {
                    bail!(
                        arg_name.span.clone(), "variable `{arg_name}` is not recursible";
                        @note "you may be using `rec` incorrectly. consult the documentation"
                    )
                } else {
                    bail!(arg_name.span.clone(), "variable `{arg_name}` not found in this scope")
                }
            }
        };

        log!("-> {res}");

        Ok(res)
    }

    fn check_positivity_impl(&self, this_ind: &Path, in_dom: bool) -> Result<()> {
        match self {
            Expr::TypeType { .. } | Expr::Var { .. } => (),
            Expr::Hole { .. } => {
                bail!(self.span(), "holes may not appear in positive position in constructor types");
            }
            Expr::Path { path, .. } => {
                if path == this_ind && in_dom {
                    bail!(
                        path.span(), "inductive types may not appear on the left of an arrow in their constructors";
                        @note "this condition is called 'strict positivity', and prevents certain weirdly defined inductive types that allow indirect recursion."
                    )
                }
            }
            // TODO: fix this: figure out if being sloppy here can cause unsoundness
            Expr::Fn { body, .. } => body.check_positivity_impl(this_ind, in_dom)?,
            Expr::Match { arms, .. } => for arm in arms {
                arm.body.check_positivity_impl(this_ind, in_dom)?;
            },
            Expr::Rec { .. } => unimplemented!("you're trying to do something tricky, and i haven't yet figured out how to prevent that properly."),
            Expr::FnType { param, cod, .. } => {
                param.ty.check_positivity_impl(this_ind, true)?;
                cod.check_positivity_impl(this_ind, in_dom)?;
            },
            Expr::FnApp { func, arg, .. } => {
                func.check_positivity_impl(this_ind, in_dom)?;
                arg.check_positivity_impl(this_ind, in_dom)?;
            },
        }

        Ok(())
    }

    fn check_positivity(&self, this_ind: &Path) -> Result<()> {
        self.check_positivity_impl(this_ind, false)
    }
}

fn expect_valid_inductive_def_ty(ty: &Expr) -> Result<()> {
    match ty {
        Expr::FnType { cod, .. } => expect_valid_inductive_def_ty(cod),
        Expr::TypeType { .. } => Ok(()),
        other => bail!(other.span(), "`{other}` is not a valid type for an inductive definition"),
    }
}

impl Item {
    pub fn ty(&self) -> Option<Expr> {
        log!("ty: {self}");
        match self {
            Item::Def { ty, .. } | Item::Axiom { ty, .. } => Some(ty.clone()),
            Item::Inductive { params, ty, .. } => {
                Some(ty.clone().with_fn_ty_params(params.iter().cloned()))
            }
        }
    }

    pub fn type_check(&self, path: &Path, md: &Module, mut_state: &mut MutState) -> Result<()> {
        log!("typeck: {self}");

        let state = State { md, ctx: &Context::Empty, depth: 0 };

        match self {
            Item::Def { ty, val, .. } => val.expect_ty(ty, state, mut_state)?,
            Item::Axiom { ty, .. } => {
                ty.expect_ty_ty(state, mut_state)?;
            }
            Item::Inductive { params, ty, constructors, .. } => {
                let mut ctx = Context::Empty;
                for param in params {
                    param.ty.expect_ty_ty(state.with_ctx(&ctx), mut_state)?;
                    ctx = ctx.with_var(param.id, param.ty.clone());
                }

                let ty_level = ty.expect_ty_ty(state.with_ctx(&ctx), mut_state)?;

                expect_valid_inductive_def_ty(ty)?;

                let new_ctx = Context::ThisInductive {
                    outer: Rc::new(ctx),
                    path: path.clone(),
                    ty: self.ty().expect("inductive definitions should have a type"),
                };

                for (cons_name, cons_ty) in constructors {
                    let cons_ty_level =
                        cons_ty.expect_ty_ty(state.with_ctx(&new_ctx), mut_state)?;

                    if cons_ty_level > ty_level - 1 {
                        bail!(
                            cons_ty.span(),
                            "constructor `{cons_name}` has level `Type {cons_ty_level}`, but inductive type `{path}` has level `Type {}`", ty_level - 1;
                            path.span().clone(),
                            "this exists at level `Type {}`", ty_level - 1;
                            @note "IMPORTANT: it's not you, this error message is confusing because of a weird bug that I haven't traced down yet :(";
                            @note "either your inductive definition is ill-founded, or you need to raise its type."
                        );
                    }

                    if !cons_ty.root_cod().head().is_path_to(path) {
                        bail!(
                            cons_ty.root_cod().span(),
                            "constructor for `{path}` does not return `{path}`"
                        );
                    }

                    let mut cons_ty = cons_ty.clone();
                    cons_ty.eval(state.with_ctx(&new_ctx), mut_state)?;
                    for param in cons_ty.fn_ty_params() {
                        param.ty.check_positivity(path)?;
                    }
                }
            }
        }

        Ok(())
    }
}

impl Module {
    pub fn type_check_root(self) -> Result<Self> {
        let mut mut_state = MutState::new();
        let mut checked_module = Module::new();

        for (path, mut item) in self.items {
            item.type_check(&path, &checked_module, &mut mut_state)?;
            item.eval(&mut checked_module, &mut mut_state)?;

            checked_module.items.insert(path, item);
        }

        // TODO: this could be sped up easily with a visited-set but im lazy
        // check that inference suceeded
        for &(id, span) in &mut_state.all_holes {
            let hole_expr = Expr::Hole { id, span };
            let resolved = mut_state.resolve_hole(&hole_expr);
            if let Expr::Hole { .. } = resolved {
                bail!(
                    span, "inference underdetermined";
                    resolved.span(), "resolved to this hole which did not resolve further"
                );
            }
        }

        Ok(checked_module)
    }
}
