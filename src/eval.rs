mod shadow_map;

use crate::{ast::Definition, eval::shadow_map::ShadowMap};

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    iter,
};

use anyhow::{bail, Context as _};

use tracing::{event, instrument, Level};

#[derive(Clone, Debug)]
pub struct InductiveDefinition {
    pub name: String,
    pub constructors: HashMap<String, ConstructorDefinition>,
}

#[derive(Clone, Debug)]
pub struct ConstructorDefinition {
    pub args: Vec<(String, Expr)>,
    pub codomain: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branch {
    pub arguments: Vec<String>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionAbstraction {
    pub var: String,
    pub domain: Box<Expr>,
    pub open_term: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionApplication {
    pub function: Box<Expr>,
    pub argument: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathType {
    pub src: Box<Expr>,
    pub dst: Box<Expr>,
    pub ty: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionType {
    pub var: String,
    pub domain: Box<Expr>,
    pub codomain: Box<Expr>,
}

impl FunctionType {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitExpr {
    pub arg: Box<Expr>,
    pub var: String,
    pub result_ty: Box<Expr>,
    pub branches: HashMap<String, Branch>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Universe,

    FunctionType(FunctionType),
    FunctionAbstraction(FunctionAbstraction),
    FunctionApplication(FunctionApplication),

    PathType(PathType),

    Ident(String),

    Split(SplitExpr),
    RecursiveCall(String),
}

impl Expr {
    fn application_root(&self) -> &Self {
        match self {
            Self::FunctionApplication(a) => a.function.application_root(),
            other => other,
        }
    }

    fn eq_up_to_var_names_impl(subs: &mut HashMap<String, String>, lhs: &Self, rhs: &Self) -> bool {
        let eq_with_substitution =
            |subs: &mut HashMap<String, String>, before: &String, after: &String, l, r| {
                let prev = subs.insert(before.clone(), after.clone());
                let res = Self::eq_up_to_var_names_impl(subs, l, r);
                subs.remove(before);
                if let Some(prev) = prev {
                    subs.insert(before.clone(), prev);
                }
                res
            };

        match (lhs, rhs) {
            (Expr::Universe, Expr::Universe) => true,
            (Expr::FunctionType(l), Expr::FunctionType(r)) => {
                Self::eq_up_to_var_names_impl(subs, &l.domain, &r.domain)
                    && eq_with_substitution(subs, &l.var, &r.var, &l.codomain, &r.codomain)
            }
            (Expr::FunctionAbstraction(l), Expr::FunctionAbstraction(r)) => {
                Self::eq_up_to_var_names_impl(subs, &l.domain, &r.domain)
                    && eq_with_substitution(subs, &l.var, &r.var, &l.open_term, &r.open_term)
            }
            (Expr::FunctionApplication(l), Expr::FunctionApplication(r)) => {
                Self::eq_up_to_var_names_impl(subs, &l.function, &r.function)
                    && Self::eq_up_to_var_names_impl(subs, &l.argument, &r.argument)
            }
            (Expr::PathType(l), Expr::PathType(r)) => {
                Self::eq_up_to_var_names_impl(subs, &l.src, &r.src)
                    && Self::eq_up_to_var_names_impl(subs, &l.dst, &r.dst)
                    && Self::eq_up_to_var_names_impl(subs, &l.ty, &r.ty)
            }
            (Expr::Ident(l), Expr::Ident(r)) => subs.get(l as &str).map_or(l == r, |l| l == r),
            (Expr::Split(l), Expr::Split(r)) => {
                let match_same_constructors = l.branches.keys().all(|c| r.branches.contains_key(c))
                    && r.branches.keys().all(|c| l.branches.contains_key(c));
                let capture_same_args = l
                    .branches
                    .iter()
                    .all(|(c, b)| b.arguments.len() == r.branches[c].arguments.len());
                todo!();
                Self::eq_up_to_var_names_impl(subs, &l.arg, &r.arg)
                    && eq_with_substitution(subs, &l.var, &r.var, &l.result_ty, &r.result_ty)
            }
            (Expr::RecursiveCall(l), Expr::RecursiveCall(r)) => {
                subs.get(l as &str).map_or(l == r, |l| l == r)
            }
            _ => false,
        }
    }

    pub fn eq_up_to_var_names(lhs: &Self, rhs: &Self) -> bool {
        Self::eq_up_to_var_names_impl(&mut HashMap::new(), lhs, rhs)
    }
}

pub struct Context {
    definitions: ShadowMap<String, Definition>,
    inductive_definitions: ShadowMap<String, InductiveDefinition>,
    bound_variables: ShadowMap<String, Expr>,
    primitives: ShadowMap<String, Expr>,
    recursable_variables: ShadowMap<String, SplitExpr>,
}

impl Context {
    pub fn prelude() -> Self {
        let mut primitives = ShadowMap::new();
        primitives.insert(
            "refl".to_string(),
            Expr::function_type(
                "A".to_string(),
                Expr::Universe,
                Expr::function_type(
                    "x".to_string(),
                    Expr::Ident("A".to_string()),
                    Expr::path_type(
                        Expr::Ident("x".to_string()),
                        Expr::Ident("x".to_string()),
                        Expr::Ident("A".to_string()),
                    ),
                ),
            ),
        );

        Self {
            definitions: ShadowMap::new(),
            inductive_definitions: ShadowMap::new(),
            bound_variables: ShadowMap::new(),
            primitives,
            recursable_variables: ShadowMap::new(),
        }
    }

    pub fn exprs_are_equivalent(&mut self, lhs: Expr, rhs: Expr) -> anyhow::Result<bool> {
        let context = format!("while checking equality of\n  {lhs}\nand\n  {rhs}");

        let lhs_evaluated = self.evaluate(lhs).context(context.clone())?;
        let rhs_evaluated = self.evaluate(rhs).context(context)?;

        Ok(Expr::eq_up_to_var_names(&lhs_evaluated, &rhs_evaluated))
    }

    pub fn type_check_definition(&mut self, def: &Definition) -> anyhow::Result<()> {
        match self.type_of(&def.ty)? {
            Expr::Universe => (),
            other => bail!("in definition of '{}': declared type '{}' is expected to be of type Type, but was found to have type {}", def.name, def.ty, other), 
        };

        let actual_type = self.type_of(&def.value)?;

        if !self.exprs_are_equivalent(*def.ty.clone(), actual_type.clone())? {
            bail!(
                "declared type\n  {}\ndoes not match actual type\n  {actual_type}\nevaluated forms:\n  {}\n  {}",
                def.ty,
                self.evaluate(*def.ty.clone())?,
                self.evaluate(actual_type.clone())?,
            );
        }

        Ok(())
    }

    pub fn type_check_inductive_definition(
        &mut self,
        def: &InductiveDefinition,
    ) -> anyhow::Result<()> {
        self.bound_variables
            .insert(def.name.clone(), Expr::Universe);
        for (name, constructor_def) in &def.constructors {
            for (arg, ty) in &constructor_def.args {
                if self
                    .type_of(&ty)
                    .with_context(|| format!("in definition of constructor '{name}'"))?
                    != Expr::Universe
                {
                    bail!("expected type of argument '{arg}' to be a type");
                }
            }

            if constructor_def.codomain != Expr::Ident(def.name.clone()) {
                bail!("codomain of constructor '{name}' is not '{}'", def.name);
            }
        }
        self.bound_variables.remove(&def.name);
        Ok(())
    }

    #[instrument(skip_all, fields(name = def.name))]
    pub fn add_definition(&mut self, def: Definition) -> anyhow::Result<()> {
        self.type_check_definition(&def)
            .with_context(|| format!("in definition of {}", def.name))?;
        // TODO: where should this evaluation happen?
        let def_value_evaluated = self
            .evaluate(*def.value)
            .with_context(|| format!("while evaluating definition of {}", def.name))?;
        self.definitions.insert(
            def.name.clone(),
            Definition {
                value: Box::new(def_value_evaluated),
                ..def
            },
        );
        Ok(())
    }

    pub fn add_inductive_definition(&mut self, def: InductiveDefinition) -> anyhow::Result<()> {
        self.type_check_inductive_definition(&def)
            .with_context(|| format!("in definition of {}", def.name))?;

        self.inductive_definitions
            .insert(def.name.clone(), def.clone());

        for (constructor_name, constructor_def) in def.constructors {
            let constructor_ty = constructor_def
                .args
                .into_iter()
                .rfold(Expr::Ident(def.name.clone()), |cod, (name, arg_ty)| {
                    Expr::function_type(name, arg_ty, cod)
                });

            self.primitives
                .insert(constructor_name.clone(), constructor_ty);
        }

        Ok(())
    }

    fn type_of_with_var(&mut self, expr: &Expr, var: String, ty: Expr) -> anyhow::Result<Expr> {
        self.bound_variables.insert(var.clone(), ty);
        let res = self.type_of(expr);
        self.bound_variables.remove(&var);
        res
    }

    #[instrument(skip(self), level = "trace", fields(%expr, ?name, %ty, %val), ret(Display), err)]
    fn evaluate_with_definition(
        &mut self,
        expr: Expr,
        name: String,
        ty: Expr,
        val: Expr,
    ) -> anyhow::Result<Expr> {
        self.definitions.insert(
            name.clone(),
            Definition {
                name: name.clone(),
                ty: Box::new(ty),
                value: Box::new(val),
            },
        );

        let res = self.evaluate(expr);

        self.definitions.remove(&name);

        res
    }

    #[instrument(skip(self), level = "trace", fields(%expr), ret(Display), err)]
    pub fn type_of(&mut self, expr: &Expr) -> anyhow::Result<Expr> {
        let context = || format!("while type checking: {expr}");

        Ok(match expr {
            Expr::Universe => Expr::Universe,
            Expr::FunctionType(fn_ty) => {
                let dom_ty = self.type_of(&fn_ty.domain).with_context(context)?;
                if dom_ty != Expr::Universe {
                    bail!("expected domain to be a type, but found to be of type {dom_ty}");
                }
                let cod_ty = self
                    .type_of_with_var(&fn_ty.codomain, fn_ty.var.clone(), *fn_ty.domain.clone())
                    .with_context(context)?;
                if cod_ty != Expr::Universe {
                    bail!("expected domain to be a type, but found to be of type {cod_ty}");
                }
                Expr::Universe
            }
            Expr::FunctionAbstraction(FunctionAbstraction {
                var: variable,
                domain,
                open_term,
            }) => {
                match self.type_of(&domain.clone()).with_context(context)? {
                    Expr::Universe => (),
                    other => bail!(
                        "`{domain}` is expected to be a type, but was found to have type `{other}`"
                    ),
                };

                Expr::FunctionType(FunctionType {
                    var: variable.clone(),
                    domain: domain.clone(),
                    codomain: Box::new(self.type_of_with_var(
                        open_term,
                        variable.clone(),
                        *domain.clone(),
                    )?),
                })
            }
            Expr::FunctionApplication(FunctionApplication { function, argument }) => {
                let arg_type = self.type_of(&argument.clone()).with_context(context)?;
                match self.type_of(&function.clone()).with_context(context)? {
                    Expr::FunctionType (FunctionType {
                        var: variable,
                        domain,
                        codomain,
                    }) => {
                        if self.exprs_are_equivalent(arg_type.clone(), *domain.clone()).with_context(context)? {
                            self.evaluate_with_definition(
                                *codomain,
                                variable,
                                *domain,
                                *argument.clone(),
                            ).with_context(context)?
                        } else {
                            bail!("argument `{argument}`: expected type `{domain}`, found `{arg_type}`")
                        }
                    }
                    other => bail!(
                        "`{function}` is expected to be a function, but was found to have type `{other}`"
                    ),
                }
            }
            Expr::PathType(p_ty) => {
                let ty_ty = self.type_of(&p_ty.ty).with_context(context)?;
                if ty_ty != Expr::Universe {
                    bail!("ty: expected type, found {ty_ty}");
                }

                let src_ty = self.type_of(&p_ty.src).with_context(context)?;
                // TODO: we don't need to evaluate `ty` twice here
                if !self
                    .exprs_are_equivalent(src_ty.clone(), *p_ty.ty.clone())
                    .with_context(context)?
                {
                    bail!("src: expected type {}, found {src_ty}", p_ty.ty);
                }
                let dst_ty = self.type_of(&p_ty.dst).with_context(context)?;
                if !self
                    .exprs_are_equivalent(dst_ty.clone(), *p_ty.ty.clone())
                    .with_context(context)?
                {
                    bail!("dst: expected type {}, found {src_ty}", p_ty.ty);
                }
                Expr::Universe
            }
            Expr::Ident(name) => {
                if let Some(ty) = self.bound_variables.get(name) {
                    ty.clone()
                } else if let Some(def) = self.definitions.get(name) {
                    *def.ty.clone()
                } else if let Some(ty) = self.primitives.get(name) {
                    ty.clone()
                } else if self.inductive_definitions.contains_key(name) {
                    Expr::Universe
                } else {
                    bail!("could not find `{name}` in this scope")
                }
            }
            Expr::Split(split) => self.type_of_split(split)?,
            Expr::RecursiveCall(argument) => {
                let Some(split) = self.recursable_variables.get(argument).cloned() else {
                    unreachable!("couldn't find recursable variable '{argument}' in scope");
                };

                self.evaluate_with_definition(
                    *split.result_ty,
                    split.var,
                    self.bound_variables
                        .get(argument)
                        .expect("branch arguments should be bound")
                        .clone(),
                    Expr::Ident(argument.clone()),
                )
                .with_context(context)?
            }
        })
    }

    fn type_of_split(&mut self, split: &SplitExpr) -> anyhow::Result<Expr> {
        let arg_ty = self.type_of(&split.arg)?;
        let arg_ty_root = arg_ty.application_root();

        let inductive_def = match arg_ty_root {
            Expr::Ident(ref name) => self
                .inductive_definitions
                .get(name)
                .cloned()
                .with_context(|| format!("cannot find inductive definition {name} in scope"))?,
            other => bail!("cannot split over non-inductive type `{other}`"),
        };

        if split.branches.len() != inductive_def.constructors.len() {
            bail!(
                "expected {} branches, found {}",
                inductive_def.constructors.len(),
                split.branches.len()
            );
        }

        for (constructor, branch) in &split.branches {
            let constructor_def =
                inductive_def
                    .constructors
                    .get(constructor)
                    .with_context(|| {
                        format!(
                            "{} has no such constructor {constructor}",
                            inductive_def.name
                        )
                    })?;

            if branch.arguments.len() != constructor_def.args.len() {
                bail!(
                    "constructor {} has {} arguments, but {} were captured",
                    inductive_def.name,
                    constructor_def.args.len(),
                    branch.arguments.len(),
                );
            }

            self.bound_variables.push_scope();
            self.recursable_variables.push_scope();

            for (argument, (_, ty)) in iter::zip(&branch.arguments, &constructor_def.args) {
                self.bound_variables.insert(argument.clone(), ty.clone());

                if ty == &arg_ty {
                    self.recursable_variables
                        .insert(argument.clone(), split.clone());
                }
            }

            let branch_ty = self.type_of(&branch.value)?;

            // if the codomain is dependent on the variable that we're splitting over, we need
            // only give a proof for terms arising from the constructor we're currently matching
            // TODO: check if this matches induction in HoTT
            let branch_expected_ty = self
                .evaluate_with_definition(
                    *split.result_ty.clone(),
                    split.var.clone(),
                    arg_ty.clone(),
                    branch
                        .arguments
                        .clone()
                        .iter()
                        .fold(Expr::Ident(constructor.clone()), |acc, arg| {
                            Expr::function_application(acc, vec![Expr::Ident(arg.clone())])
                        }),
                )
                .with_context(|| {
                    format!("while determining expected type of branch '{constructor}'")
                })?;

            if !self.exprs_are_equivalent(branch_ty.clone(), branch_expected_ty.clone())? {
                bail!("branch {constructor} is expected to have type `{branch_expected_ty}`, but was found to have type `{branch_ty}`");
            }

            self.recursable_variables.pop_scope();
            self.bound_variables.pop_scope();
        }

        self.evaluate_with_definition(
            *split.result_ty.clone(),
            split.var.clone(),
            arg_ty,
            *split.arg.clone(),
        )
    }

    #[instrument(skip(self), level = "trace", fields(%expr), ret(Display), err)]
    pub fn evaluate(&mut self, expr: Expr) -> anyhow::Result<Expr> {
        let display_expr = expr.clone();
        let context = || format!("while evaluating: {display_expr}");

        Ok(match expr {
            Expr::Universe => Expr::Universe,
            Expr::FunctionType(FunctionType {
                var: variable,
                domain,
                codomain,
            }) => {
                self.bound_variables
                    .insert(variable.clone(), *domain.clone());

                let codomain_evaluated = self.evaluate(*codomain).with_context(context)?;

                self.bound_variables.remove(&variable);

                Expr::FunctionType(FunctionType {
                    var: variable,
                    domain: Box::new(self.evaluate(*domain).with_context(context)?),
                    codomain: Box::new(codomain_evaluated),
                })
            }
            Expr::FunctionAbstraction(FunctionAbstraction {
                var: variable,
                domain,
                open_term,
            }) => {
                self.bound_variables
                    .insert(variable.clone(), *domain.clone());

                let open_term_evaluated = self.evaluate(*open_term).with_context(context)?;

                self.bound_variables.remove(&variable);

                Expr::FunctionAbstraction(FunctionAbstraction {
                    var: variable,
                    domain: Box::new(self.evaluate(*domain).with_context(context)?),
                    open_term: Box::new(open_term_evaluated),
                })
            }
            Expr::FunctionApplication(FunctionApplication { function, argument }) => {
                let argument = self.evaluate(*argument).with_context(context)?;
                match self.evaluate(*function).with_context(context)? {
                    Expr::FunctionAbstraction(FunctionAbstraction {
                        var,
                        domain,
                        // TODO: should this do type-checking before simplifying?
                        open_term,
                    }) => self
                        .evaluate_with_definition(*open_term, var, *domain, argument)
                        .with_context(context)?,
                    other => Expr::FunctionApplication(FunctionApplication {
                        function: Box::new(other),
                        argument: Box::new(argument),
                    }),
                }
            }
            Expr::PathType(PathType { src, dst, ty }) => Expr::PathType(PathType {
                src: Box::new(self.evaluate(*src).with_context(context)?),
                dst: Box::new(self.evaluate(*dst).with_context(context)?),
                ty: Box::new(self.evaluate(*ty).with_context(context)?),
            }),
            Expr::Ident(name) => {
                if self.bound_variables.contains_key(&name)
                    || self.primitives.contains_key(&name)
                    || self.inductive_definitions.contains_key(&name)
                {
                    Expr::Ident(name)
                } else if let Some(def) = self.definitions.get(&name) {
                    *def.value.clone()
                } else {
                    bail!("could not find `{name}` in this scope")
                }
            }
            Expr::Split(split) => self.evaluate_split(&split)?,
            Expr::RecursiveCall(argument) => {
                let split_expr = self.recursable_variables.get(&argument).with_context(|| {
                    format!("recursable variable '{argument}' not found in this scope")
                })?;

                self.evaluate(Expr::Split(SplitExpr {
                    arg: Box::new(Expr::Ident(argument)),
                    ..split_expr.clone()
                }))
                .with_context(context)?
            }
        })
    }

    fn evaluate_split(&mut self, split: &SplitExpr) -> anyhow::Result<Expr> {
        let arg_ty = match self.type_of(&split.arg).context("in argument of split")? {
            Expr::Ident(arg_ty) => arg_ty,
            other => bail!("cannot split over non-inductive type `{other}`"),
        };

        let Some(inductive_def) = self.inductive_definitions.get(&arg_ty).cloned() else {
            bail!("no inductive type '{arg_ty}' in scope");
        };

        let split_arg = self
            .evaluate(*split.arg.clone())
            .context("in argument of split")?;

        let arg_constructor = match split_arg.application_root() {
            Expr::Ident(c) => c.clone(),
            // TODO: is it reasonable for this to happen? seems likely...
            _ => panic!("split arg not properly reduced"),
        };

        let Some(constructor_def) = inductive_def.constructors.get(&arg_constructor) else {
            event!(
                Level::DEBUG,
                "{arg_constructor} is not a constructor of {}",
                inductive_def.name
            );
            return Ok(Expr::Split(SplitExpr {
                arg: Box::new(split_arg),
                ..split.clone()
            }));
        };

        let Some(branch) = split.branches.get(&arg_constructor) else {
            bail!("no branch matching constructor '{arg_constructor}'");
        };

        // TODO: is there a better way to do this? recursion perhaps?
        // the while-let is actually kind of elegant.
        let mut split_arg = split_arg;
        let mut branch_args = branch.arguments.iter();
        let mut constructor_args = constructor_def.args.iter();
        while let Expr::FunctionApplication(app) = split_arg {
            let branch_arg = branch_args
                .next_back()
                .expect("type check should ensure that the right number of args are matched");

            let (_, constructor_arg_ty) = constructor_args
                .next_back()
                .expect("type check should ensure that the right number of args are matched");

            self.definitions.insert(
                branch_arg.clone(),
                Definition {
                    name: branch_arg.clone(),
                    ty: Box::new(constructor_arg_ty.clone()),
                    value: app.argument,
                },
            );

            if constructor_arg_ty == &Expr::Ident(arg_ty.clone()) {
                self.recursable_variables
                    .insert(branch_arg.clone(), split.clone());
            }

            split_arg = *app.function;
        }

        let res = self
            .evaluate(branch.value.clone())
            .with_context(|| format!("in {}", Expr::Split(split.clone())))?;

        for branch_arg in &branch.arguments {
            self.definitions.remove(branch_arg);
            self.recursable_variables.remove(branch_arg);
        }

        Ok(res)
    }
}
