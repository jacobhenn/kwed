use std::collections::{HashMap, HashSet};

use anyhow::{bail, Context as _};

use crate::ast::{Branch, Definition, Expr, InductiveDefinition, SplitExpr};

impl Expr {
    pub fn substitute(self, sub_var: String, sub: Self) -> Self {
        match self {
            Expr::Universe => Expr::Universe,
            Expr::FunctionType {
                variable,
                domain,
                codomain,
            } => {
                if variable == sub_var {
                    Expr::FunctionType {
                        variable,
                        domain,
                        codomain,
                    }
                } else {
                    Expr::FunctionType {
                        variable,
                        domain: Box::new(domain.substitute(sub_var.clone(), sub.clone())),
                        codomain: Box::new(codomain.substitute(sub_var, sub)),
                    }
                }
            }
            // TODO: how to deal with shadowing
            Expr::FunctionAbstraction {
                variable,
                domain,
                open_term,
            } => {
                if variable == sub_var {
                    Expr::FunctionAbstraction {
                        variable,
                        domain,
                        open_term,
                    }
                } else {
                    Expr::FunctionAbstraction {
                        variable,
                        domain: Box::new(domain.substitute(sub_var.clone(), sub.clone())),
                        open_term: Box::new(open_term.substitute(sub_var, sub)),
                    }
                }
            }
            Expr::FunctionApplication { function, argument } => Expr::FunctionApplication {
                function: Box::new(function.substitute(sub_var.clone(), sub.clone())),
                argument: Box::new(argument.substitute(sub_var.clone(), sub.clone())),
            },
            Expr::PathType { src, dst, ty } => Expr::PathType {
                src: Box::new(src.substitute(sub_var.clone(), sub.clone())),
                dst: Box::new(dst.substitute(sub_var.clone(), sub.clone())),
                ty: Box::new(ty.substitute(sub_var, sub)),
            },
            Expr::Ident(ident) => {
                if ident == sub_var {
                    sub
                } else {
                    Expr::Ident(ident)
                }
            }
            Expr::Split(SplitExpr {
                arg,
                var,
                result_ty,
                branches,
            }) => Expr::Split(SplitExpr {
                arg: Box::new(arg.substitute(sub_var.clone(), sub.clone())),
                var: var.clone(),
                result_ty: if var == sub_var {
                    result_ty
                } else {
                    Box::new(result_ty.substitute(sub_var.clone(), sub.clone()))
                },
                branches: branches
                    .into_iter()
                    .map(
                        |Branch {
                             constructor,
                             arguments,
                             value,
                         }| {
                            Branch {
                                constructor,
                                arguments: arguments.clone(),
                                value: if arguments.contains(&sub_var) {
                                    value
                                } else {
                                    value.substitute(sub_var.clone(), sub.clone())
                                },
                            }
                        },
                    )
                    .collect(),
            }),
            // `rec{a}` should be treated as a single, opaque symbol
            Expr::RecursiveCall { argument } => Expr::RecursiveCall { argument },
        }
    }
}

impl Branch {
    pub fn substitute(self, sub_var: String, sub: Expr) -> Self {
        if self.arguments.contains(&sub_var) {
            Branch { ..self }
        } else {
            Branch {
                value: self.value.substitute(sub_var, sub),
                ..self
            }
        }
    }
}

pub struct Context {
    definitions: HashMap<String, Definition>,
    inductive_definitions: HashMap<String, InductiveDefinition>,
    bound_variables: HashMap<String, Expr>,
    primitives: HashMap<String, Expr>,
    recursable_variables: HashMap<String, SplitExpr>,
}

impl Context {
    pub fn prelude() -> Self {
        let mut primitives = HashMap::new();
        primitives.insert(
            "refl".to_string(),
            Expr::FunctionType {
                variable: "A".to_string(),
                domain: Box::new(Expr::Universe),
                codomain: Box::new(Expr::FunctionType {
                    variable: "x".to_string(),
                    domain: Box::new(Expr::Ident("A".to_string())),
                    codomain: Box::new(Expr::PathType {
                        src: Box::new(Expr::Ident("x".to_string())),
                        dst: Box::new(Expr::Ident("x".to_string())),
                        ty: Box::new(Expr::Ident("A".to_string())),
                    }),
                }),
            },
        );

        Self {
            definitions: HashMap::new(),
            inductive_definitions: HashMap::new(),
            bound_variables: HashMap::new(),
            primitives,
            recursable_variables: HashMap::new(),
        }
    }

    fn type_of_with_var(&mut self, expr: &Expr, var: String, var_ty: Expr) -> anyhow::Result<Expr> {
        self.bound_variables.insert(var.clone(), var_ty);
        let res = self.type_of(expr);
        self.bound_variables.remove(&var);
        res
    }

    pub fn exprs_are_equivalent(&mut self, l_expr: Expr, r_expr: Expr) -> anyhow::Result<bool> {
        let context = format!("while checking equality of\n  {l_expr}\nand\n  {r_expr}");

        let l_expr_evaluated = self.evaluate(l_expr).context(context.clone())?;
        let r_expr_evaluated = self.evaluate(r_expr).context(context)?;

        self.exprs_are_equivalent_impl(l_expr_evaluated, r_expr_evaluated)
    }

    fn exprs_are_equivalent_impl(&mut self, l_expr: Expr, r_expr: Expr) -> anyhow::Result<bool> {
        Ok(match (l_expr, r_expr) {
            (Expr::Universe, Expr::Universe) => true,
            (
                Expr::FunctionType {
                    variable: l_variable,
                    domain: l_domain,
                    codomain: l_codomain,
                },
                Expr::FunctionType {
                    variable: r_variable,
                    domain: r_domain,
                    codomain: r_codomain,
                },
            ) => {
                self.exprs_are_equivalent_impl(*l_domain, *r_domain)?
                    && self.exprs_are_equivalent_impl(
                        *l_codomain,
                        r_codomain.substitute(r_variable, Expr::Ident(l_variable)),
                    )?
            }
            (
                Expr::FunctionAbstraction {
                    variable: l_variable,
                    domain: l_domain,
                    open_term: l_open_term,
                },
                Expr::FunctionAbstraction {
                    variable: r_variable,
                    domain: r_domain,
                    open_term: r_open_term,
                },
            ) => {
                self.exprs_are_equivalent_impl(*l_domain, *r_domain)?
                    && self.exprs_are_equivalent_impl(
                        *l_open_term,
                        r_open_term.substitute(r_variable, Expr::Ident(l_variable)),
                    )?
            }
            (
                Expr::FunctionApplication {
                    function: l_function,
                    argument: l_argument,
                },
                Expr::FunctionApplication {
                    function: r_function,
                    argument: r_argument,
                },
            ) => {
                self.exprs_are_equivalent_impl(*l_function, *r_function)?
                    && self.exprs_are_equivalent_impl(*l_argument, *r_argument)?
            }
            (
                Expr::PathType {
                    src: l_src,
                    dst: l_dst,
                    ty: l_ty,
                },
                Expr::PathType {
                    src: r_src,
                    dst: r_dst,
                    ty: r_ty,
                },
            ) => {
                self.exprs_are_equivalent_impl(*l_src, *r_src)?
                    && self.exprs_are_equivalent_impl(*l_dst, *r_dst)?
                    && self.exprs_are_equivalent_impl(*l_ty, *r_ty)?
            }
            (Expr::Ident(l), Expr::Ident(r)) => l == r,
            _ => false,
        })
    }

    pub fn type_check_definition(&mut self, def: &Definition) -> anyhow::Result<()> {
        let actual_type = self.type_of(&def.value)?;

        if !self.exprs_are_equivalent(*def.ty.clone(), actual_type.clone())? {
            bail!(
                "declared type\n  {}\ndoes not match actual type\n  {actual_type}",
                def.ty
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
        for constructor_definition in &def.constructors {
            for (arg_name, arg_ty) in &constructor_definition.args {
                match self.type_of(&arg_ty).with_context(|| format!("argument {arg_name}"))? {
                    Expr::Universe => (),
                    other => bail!("constructor {}: type of argument {arg_name} is expected to be a type, but was found to be of type\n  {other}", constructor_definition.name),
                }
            }
        }
        self.bound_variables.remove(&def.name);
        Ok(())
    }

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

        for constructor_definition in def.constructors {
            let constructor_type = constructor_definition.args.into_iter().rfold(
                Expr::Ident(def.name.clone()),
                |acc, (name, ty)| Expr::FunctionType {
                    variable: name,
                    domain: Box::new(ty),
                    codomain: Box::new(acc),
                },
            );

            self.primitives
                .insert(constructor_definition.name.clone(), constructor_type);
        }

        Ok(())
    }

    pub fn type_of(&mut self, expr: &Expr) -> anyhow::Result<Expr> {
        let context = || format!("in {expr}");

        Ok(match expr {
            Expr::Universe => Expr::Universe,
            Expr::FunctionType { .. } => Expr::Universe,
            Expr::FunctionAbstraction {
                variable,
                domain,
                open_term,
            } => {
                match self.type_of(&domain.clone()).with_context(context)? {
                    Expr::Universe => (),
                    other => bail!(
                        "`{domain}` is expected to be a type, but was found to have type `{other}`"
                    ),
                };

                Expr::FunctionType {
                    variable: variable.clone(),
                    domain: domain.clone(),
                    codomain: Box::new(self.type_of_with_var(
                        open_term,
                        variable.clone(),
                        *domain.clone(),
                    )?),
                }
            }
            Expr::FunctionApplication { function, argument } => {
                let arg_type = self.type_of(&argument.clone()).with_context(context)?;
                match self.type_of(&function.clone()).with_context(context)? {
                    Expr::FunctionType {
                        variable,
                        domain,
                        codomain,
                    } => {
                        if self.exprs_are_equivalent(arg_type.clone(), *domain.clone()).with_context(context)? {
                            codomain.substitute(variable, *argument.clone())
                        } else {
                            bail!("argument `{argument}` is expected to have type `{domain}`, but was found to have type `{arg_type}`")
                        }
                    }
                    other => bail!(
                        "`{function}` is expected to be a function, but was found to have type `{other}`"
                    ),
                }
            }
            Expr::PathType { .. } => Expr::Universe,
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
            Expr::Split(SplitExpr {
                arg,
                var,
                result_ty,
                branches,
            }) => {
                let this_split = SplitExpr {
                    arg: arg.clone(),
                    var: var.clone(),
                    result_ty: result_ty.clone(),
                    branches: branches.clone(),
                };

                let arg_ty = self.type_of(arg)?;

                let inductive_definition = match arg_ty {
                    Expr::Ident(ref name) => {
                        if let Some(def) = self.inductive_definitions.get(name) {
                            def.clone()
                        } else {
                            bail!("cannot find inductive definition {name} in scope")
                        }
                    }
                    other => bail!("cannot split over non-inductive type `{other}`"),
                };

                if branches.len() != inductive_definition.constructors.len() {
                    bail!(
                        "expected {} branches, found {}",
                        inductive_definition.constructors.len(),
                        branches.len()
                    );
                }

                let mut checked_branches = HashSet::new();
                for branch in branches {
                    let Some(constructor_def) = inductive_definition
                        .constructors
                        .iter()
                        .find(|def| def.name == branch.constructor)
                    else {
                        bail!(
                            "{} has no such constructor {}",
                            inductive_definition.name,
                            branch.constructor
                        );
                    };

                    if !checked_branches.insert(branch.constructor.clone()) {
                        bail!("constructor {} is matched twice", branch.constructor);
                    }

                    if branch.arguments.len() != constructor_def.args.len() {
                        bail!(
                            "constructor {} has {} arguments, but {} were captured",
                            constructor_def.name,
                            constructor_def.args.len(),
                            branch.arguments.len(),
                        );
                    }

                    for (argument, (_, ty)) in
                        std::iter::zip(&branch.arguments, &constructor_def.args)
                    {
                        if self
                            .bound_variables
                            .insert(argument.clone(), ty.clone())
                            .is_some()
                        {
                            bail!("'{argument}' is already defined");
                        }

                        if ty == &arg_ty {
                            self.recursable_variables
                                .insert(argument.clone(), this_split.clone());
                        }
                    }

                    let branch_ty = self.type_of(&branch.value)?;

                    // if the codomain is dependent on the variable that we're splitting over, we need
                    // only give a proof for terms arising from the constructor we're currently matching
                    // TODO: check if this matches induction in HoTT
                    let branch_expected_ty = result_ty.clone().substitute(
                        var.clone(),
                        branch.arguments.clone().iter().fold(
                            Expr::Ident(branch.constructor.clone()),
                            |acc, arg| Expr::FunctionApplication {
                                function: Box::new(acc),
                                argument: Box::new(Expr::Ident(arg.clone())),
                            },
                        ),
                    );

                    if !self.exprs_are_equivalent(branch_ty.clone(), branch_expected_ty.clone())? {
                        bail!("branch {} is expected to have type `{branch_expected_ty}`, but was found to have type `{branch_ty}`", branch.constructor);
                    }

                    for argument in &branch.arguments {
                        self.recursable_variables.remove(argument);
                        self.bound_variables.remove(argument);
                    }
                }

                result_ty.clone().substitute(var.clone(), *arg.clone())
            }
            Expr::RecursiveCall { argument } => {
                let Some(SplitExpr { var, result_ty, .. }) =
                    self.recursable_variables.get(argument).cloned()
                else {
                    unreachable!("couldn't find recursable variable '{argument}' in scope");
                };

                result_ty
                    .clone()
                    .substitute(var.clone(), Expr::Ident(argument.clone()))
            }
        })
    }

    pub fn evaluate(&mut self, expr: Expr) -> anyhow::Result<Expr> {
        let display_expr = expr.clone();
        let context = || format!("in evaluation of {display_expr}");

        Ok(match expr {
            Expr::Universe => Expr::Universe,
            Expr::FunctionType {
                variable,
                domain,
                codomain,
            } => {
                let prev_binding = self
                    .bound_variables
                    .insert(variable.clone(), *domain.clone());

                let codomain_evaluated = self.evaluate(*codomain).with_context(context)?;

                self.bound_variables.remove(&variable);
                if let Some(prev_binding) = prev_binding {
                    self.bound_variables.insert(variable.clone(), prev_binding);
                }

                Expr::FunctionType {
                    variable,
                    domain: Box::new(self.evaluate(*domain).with_context(context)?),
                    codomain: Box::new(codomain_evaluated),
                }
            }
            Expr::FunctionAbstraction {
                variable,
                domain,
                open_term,
            } => {
                let prev_binding = self
                    .bound_variables
                    .insert(variable.clone(), *domain.clone());

                let open_term_evaluated = self.evaluate(*open_term).with_context(context)?;

                self.bound_variables.remove(&variable);
                if let Some(prev_binding) = prev_binding {
                    self.bound_variables.insert(variable.clone(), prev_binding);
                }

                Expr::FunctionAbstraction {
                    variable,
                    domain: Box::new(self.evaluate(*domain).with_context(context)?),
                    open_term: Box::new(open_term_evaluated),
                }
            }
            Expr::FunctionApplication { function, argument } => {
                let argument = self.evaluate(*argument).with_context(context)?;
                match self.evaluate(*function).with_context(context)? {
                    Expr::FunctionAbstraction {
                        variable,
                        // TODO: should this do type-checking before simplifying?
                        open_term,
                        ..
                    } => self
                        .evaluate(open_term.substitute(variable, argument))
                        .with_context(context)?,
                    other => Expr::FunctionApplication {
                        function: Box::new(other),
                        argument: Box::new(argument),
                    },
                }
            }
            Expr::PathType { src, dst, ty } => Expr::PathType {
                src: Box::new(self.evaluate(*src).with_context(context)?),
                dst: Box::new(self.evaluate(*dst).with_context(context)?),
                ty: Box::new(self.evaluate(*ty).with_context(context)?),
            },
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
            Expr::Split(SplitExpr {
                arg: split_arg,
                var,
                result_ty,
                branches,
            }) => {
                let split = SplitExpr {
                    arg: split_arg.clone(),
                    var: var.clone(),
                    result_ty: result_ty.clone(),
                    branches: branches.clone(),
                };

                let arg_ty = match self
                    .type_of(&split_arg)
                    .with_context(|| format!("in split {split_arg}"))?
                {
                    Expr::Ident(arg_ty) => arg_ty,
                    other => bail!("cannot split over non-inductive type `{other}`"),
                };

                let Some(arg_ty_def) = self.inductive_definitions.get(&arg_ty).cloned() else {
                    bail!("no inductive type '{arg_ty}' in scope");
                };

                let split_arg = self
                    .evaluate(*split_arg)
                    .with_context(|| format!("argument of split {var}"))?;

                let arg_constructor = match &split_arg {
                    Expr::FunctionApplication { function, .. } => match &**function {
                        Expr::Ident(constructor) => constructor.clone(),
                        _ => return Ok(Expr::Split(split)),
                    },
                    Expr::Ident(constructor) => constructor.clone(),
                    _ => return Ok(Expr::Split(split)),
                };

                let Some(constructor_def) = arg_ty_def
                    .constructors
                    .into_iter()
                    .find(|constructor| constructor.name == arg_constructor)
                else {
                    return Ok(Expr::Split(split));
                };

                let Some(branch) = branches
                    .into_iter()
                    .find(|branch| branch.constructor == arg_constructor)
                else {
                    bail!("no branch matching constructor '{arg_constructor}'");
                };

                // TODO: is there a better way to do this? recursion perhaps?
                // the while-let is actually kind of elegant.
                let mut split_arg = split_arg;
                let mut branch_args = branch.arguments.iter();
                let mut constructor_args = constructor_def.args.iter();
                while let Expr::FunctionApplication { function, argument } = split_arg {
                    let branch_arg = branch_args.next_back().expect(
                        "type check should ensure that the right number of args are captured",
                    );

                    let (_, constructor_arg_ty) = constructor_args.next().expect(
                        "type check should ensure that the right number of args are captured",
                    );

                    self.definitions.insert(
                        branch_arg.clone(),
                        Definition {
                            name: branch_arg.clone(),
                            ty: Box::new(constructor_arg_ty.clone()),
                            value: argument,
                        },
                    );

                    if constructor_arg_ty == &Expr::Ident(arg_ty.clone()) {
                        self.recursable_variables
                            .insert(branch_arg.clone(), split.clone());
                    }

                    split_arg = *function;
                }

                let res = self.evaluate(branch.value).with_context(context)?;

                for branch_arg in branch.arguments {
                    self.definitions.remove(&branch_arg);
                    self.recursable_variables.remove(&branch_arg);
                }

                res
            }
            Expr::RecursiveCall { argument } => {
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
}
