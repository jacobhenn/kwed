use crate::{bail, err, err::Result};

use super::{
    desugared::{self, BindingParam},
    Ident, Path, Span,
};

use std::{cmp, collections::HashMap, iter, rc::Rc};

use chumsky::Parser;
use codespan_reporting::files::SimpleFiles;
use indexmap::IndexMap;

use ulid::Ulid;

const FORBIDDEN_NAMES: &[&str] = &["Super", "Lib"];

// TODO: add function to check for name duplication

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// An error node representing an expression which failed to parse.
    Error,

    TypeType {
        level: usize,
        span: Span,
    },

    Path {
        path: Path,
        level: usize,
        span: Span,
    },

    Fn {
        params: Params,
        body: Box<Self>,
        span: Span,
    },
    FnType {
        params: Params,
        cod: Box<Self>,
        span: Span,
    },
    FnApp {
        func: Box<Self>,
        args: Vec<Self>,
        named_args: Vec<(Ident, Self)>,
        span: Span,
    },

    Match {
        arg: Box<Self>,
        cod_pars: Vec<Ident>,
        cod_body: Box<Self>,
        arms: Vec<Arm>,
        span: Span,
    },
    Rec {
        arg_name: Ident,
        span: Span,
    },

    Number {
        number: i64,
        span: Span,
    },

    Let {
        name: Ident,
        val: Box<Expr>,
        body: Box<Expr>,
        span: Span,
    },
    TypedLet {
        name: Ident,
        val: Box<Expr>,
        ty: Box<Expr>,
        body: Box<Expr>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub names: Vec<Ident>,
    pub ty: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Params(pub Vec<Param>);

impl Params {
    pub fn names(&self) -> impl Iterator<Item = &Ident> {
        self.0.iter().map(|param| &param.names).flatten()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub constructor: Ident,
    pub cons_args: Vec<Ident>,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub enum Item {
    Def {
        args: Params,
        ty: Expr,
        val: Expr,
    },
    Inductive {
        params: Params,
        ty: Expr,
        constructors: Option<Vec<(Ident, Expr)>>,
    },
    Struct {
        params: Params,
        ty: Expr,
        fields: Option<Vec<(Ident, Expr)>>,
    },
    Axiom {
        ty: Expr,
    },
}

#[derive(Debug, PartialEq)]
pub struct PathTree {
    pub initial_path: Path,
    pub children: Option<Vec<PathTree>>,
}

impl PathTree {
    pub fn parent_of(&self, ident: &Ident) -> Option<Path> {
        if let Some(children) = &self.children {
            Some(Path::concat_using_rhs_span(
                self.initial_path.clone(),
                children.iter().find_map(|child| child.parent_of(ident))?,
            ))
        } else {
            (self.initial_path.last_component() == ident)
                .then_some(self.initial_path.clone().parent())
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub submodules: Vec<Ident>,
    pub imports: Vec<PathTree>,
    pub notation: HashMap<String, Expr>,
    pub items: IndexMap<Path, Item>,
}

impl Expr {
    pub(crate) fn span(&self) -> Span {
        match self {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. }
            | Expr::Let { span, .. }
            | Expr::TypedLet { span, .. }
            | Expr::Number { span, .. } => span.clone(),
        }
    }

    pub(crate) fn span_mut(&mut self) -> &mut Span {
        match self {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. }
            | Expr::Let { span, .. }
            | Expr::TypedLet { span, .. }
            | Expr::Number { span, .. } => span,
        }
    }

    pub fn rc(self) -> Rc<Self> {
        Rc::new(self)
    }
}

pub struct Desugarer {
    module: Module,
    module_name: Ident,
}

impl Desugarer {
    // TODO: desugaring is getting a little bloated; it might be a good idea at some point to
    // split this up into phases for module loading, path expansion, etc.
    fn desugar_expr(&self, expr: &Expr) -> Result<desugared::Expr> {
        Ok(match expr {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { level, span } => desugared::Expr::TypeType {
                level: *level,
                span: Some(*span),
            },
            Expr::Path { path, span, level } => {
                let resolved_path = if let Some(import_path) = self
                    .module
                    .imports
                    .iter()
                    .find_map(|path_tree| path_tree.parent_of(path.first_component()))
                {
                    Path::concat_using_rhs_span(import_path, path.clone())
                } else {
                    path.clone()
                };

                desugared::Expr::Path {
                    path: resolved_path,
                    level: *level,
                    span: Some(*span),
                }
            }
            Expr::Fn { params, body, .. } => self
                .desugar_expr(body)?
                .with_fn_params(self.desugar_params(params)?),
            Expr::FnType { params, cod, .. } => self
                .desugar_expr(cod)?
                .with_fn_ty_params(self.desugar_params(params)?),
            Expr::FnApp {
                func,
                args,
                named_args,
                span,
            } => {
                let func_desugared = self.desugar_expr(func)?;
                let mut args = args
                    .into_iter()
                    .map(|arg| self.desugar_expr(arg))
                    .collect::<Result<Vec<_>>>()?;

                if !named_args.is_empty() {
                    let desugared::Expr::Path {
                        path: func_path, ..
                    } = &func_desugared
                    else {
                        bail!(
                            Some(*span),
                            "named arguments may only be given to a function whose path is known at desugaring time";
                            func_desugared.span(), "this must be a path in order to use named arguments"
                        );
                    };

                    let func_params = self.module.get_param_names(func_path)?;

                    for (supplied_name, supplied_arg) in named_args {
                        let Some(arg_idx) =
                            func_params.iter().position(|arg| *arg == supplied_name)
                        else {
                            bail!(
                                supplied_name.span,
                                "`{func_path}` has no such argument `{supplied_name}`"
                            )
                        };

                        let arg_idx_saturated = cmp::min(arg_idx, args.len());

                        args.insert(arg_idx_saturated, self.desugar_expr(supplied_arg)?);
                    }
                }

                func_desugared.with_args(args)
            }
            Expr::Match {
                arg,
                cod_pars,
                cod_body,
                arms,
                span,
            } => desugared::Expr::Match {
                arg: self.desugar_expr(arg)?.rc(),
                cod_pars: cod_pars
                    .into_iter()
                    .map(|name| (name.clone(), Ulid::new()))
                    .collect(),
                cod_body: self.desugar_expr(cod_body)?.rc(),
                arms: arms
                    .into_iter()
                    .map(|arm| self.desugar_arm(arm))
                    .collect::<Result<_>>()?,
                span: Some(*span),
            },
            Expr::Rec { arg_name, span } => desugared::Expr::Rec {
                arg_id: Ulid::nil(),
                arg_name: arg_name.clone(),
                span: Some(*span),
            },
            Expr::Number { number, span } => {
                let Some(mut number_0) = self.module.notation.get("number-0").cloned() else {
                    bail!(Some(*span), "notation `number-0` not set");
                };

                let Some(mut number_suc) = self.module.notation.get("number-suc").cloned() else {
                    bail!(Some(*span), "notation `number-suc` not set");
                };

                *number_0.span_mut() = span.clone();
                *number_suc.span_mut() = span.clone();

                match usize::try_from(*number) {
                    Ok(n) => iter::repeat_n(self.desugar_expr(&number_suc)?, n)
                        .rfold(self.desugar_expr(&number_0)?, |acc, f| {
                            f.with_arg(acc).with_span(span.clone())
                        }),
                    Err(e) => {
                        bail!(Some(*span), "unsupported number literal: {e}")
                    }
                }
            }
            Expr::Let {
                name, val, body, ..
            } => {
                let mut res = self.desugar_expr(body)?;
                res.replace(
                    &|expr| expr.is_path_to_ident(name),
                    &self.desugar_expr(val)?,
                );
                res
            }
            Expr::TypedLet {
                name,
                val,
                ty,
                body,
                ..
            } => self
                .desugar_expr(body)?
                .with_fn_param(BindingParam::new(name.clone(), self.desugar_expr(ty)?))
                .with_arg(self.desugar_expr(val)?),
        })
    }

    fn desugar_arm(&self, arm: &Arm) -> Result<desugared::Arm> {
        Ok(desugared::Arm {
            constructor: arm.constructor.clone(),
            cons_args: arm
                .cons_args
                .iter()
                .map(|name| (name.clone(), Ulid::new()))
                .collect(),
            body: self.desugar_expr(&arm.body)?,
        })
    }

    fn desugar_struct(
        &self,
        struct_path: &Path,
        struct_def_params: &Params,
        struct_def_ty: &Expr,
        struct_def_fields: &Option<Vec<(Ident, Expr)>>,
    ) -> Result<Vec<(Path, desugared::Item)>> {
        // The canonical example used in this function's comments will be the following struct:
        //
        // ```kwed
        // struct Pair(A: Type, B: A → Type): Type {
        //     first: A,
        //     second: B first,
        // }
        // ```
        //
        // which should desugar to the following code:
        //
        // ```kwed
        // inductive Pair(A: Type, B: A → Type): Type {
        //     make: (first: A, second: B first) → Pair A B,
        // }
        //
        // def Pair.first(A: Type, B: A → Type, pair: Pair A B): A {
        //     match pair to [pair] A {
        //         make first second => first,
        //     }
        // }
        //
        // def Pair.second(A: Type, B: A → Type, pair: Pair A B): B (Pair.first A B pair) {
        //     match pair to [pair] B (Pair.first A B pair) {
        //         make first second => second,
        //     }
        // }
        // ```

        // the fields of the struct: `first: A, second: B first`
        let struct_def_fields = struct_def_fields
            .as_ref()
            .expect("error nodes should not make it to desugaring");

        // the parameters of the `make` constructor: `(first: A, second: B first)`
        let make_params = struct_def_fields
            .iter()
            .map(|(name, ty)| {
                self.desugar_expr(ty)
                    .map(|ty| BindingParam::new(name.clone(), ty))
            })
            .collect::<Result<Vec<_>>>()?;

        let desugared_struct_def_params: Vec<BindingParam> =
            self.desugar_params(struct_def_params)?;

        // the type of the `make` constructor: `(first: A, second: B first) → Pair A B`
        let make_ty = struct_path
            .clone()
            .to_expr(0)
            .with_args(
                desugared_struct_def_params
                    .iter()
                    .cloned()
                    .map(BindingParam::to_var),
            )
            .with_fn_ty_params(make_params);

        let make_ident = Ident::from_str("make");

        // the inductive definition of the struct:
        // ```kwed
        // inductive Pair(A: Type, B: A → Type): Type {
        //     make: (first: A, second: B first) → Pair A B,
        // }
        // ```
        let ind_def = desugared::Item::Inductive {
            params: desugared_struct_def_params.clone(),
            ty: self.desugar_expr(struct_def_ty)?,
            constructors: vec![(make_ident.clone(), make_ty)],
        };

        let mut ret = vec![(struct_path.clone(), ind_def)];

        // -- emit getter functions

        // the parameters of our struct, converted to variables for easy application: `A B`
        let param_vars = desugared_struct_def_params
            .iter()
            .cloned()
            .map(BindingParam::to_var);

        // the final parameter of all getters: `Pair A B`
        let getter_final_param =
            BindingParam::blank(struct_path.clone().to_expr(0).with_args(param_vars.clone()));

        // the parameters of all getters: `A: Type, B: A → Type, pair: Pair A B`
        let getter_params = desugared_struct_def_params
            .iter()
            .cloned()
            .chain([getter_final_param.clone()]);

        let prepend_struct_path = |name: &Ident| struct_path.clone().with_suffix(name.clone());

        for (field_idx, (field_name, field_ty)) in struct_def_fields.iter().enumerate() {
            // for this part of the comments, we'll focus on the second field of the struct,
            // ```
            //     second: B first,
            // ```
            // so the variables captured in this loop would be:
            //     field_name: "second",
            //     field_ty: `B first`
            //
            // remember that the getter we're trying to generate is:
            //
            // ```
            // def Pair.second(A: Type, B: A → Type, pair: Pair A B): B (Pair.first A B pair) {
            //     match pair to [pair] B (Pair.first A B pair) {
            //         make first second => second,
            //     }
            // }
            // ```

            let desugared_field_ty = self.desugar_expr(field_ty)?;

            // the return type of this getter: B (Pair.first A B pair)
            let mut getter_ret_ty = desugared_field_ty.clone();
            for name in struct_def_fields.iter().map(|(name, _ty)| name) {
                getter_ret_ty.replace(
                    &|expr: &desugared::Expr| expr.is_path_to_ident(name),
                    &prepend_struct_path(name)
                        .clone()
                        .to_expr(0)
                        .with_args(param_vars.clone())
                        .with_arg(getter_final_param.clone().to_var()),
                );
            }

            // the type of this getter: `(A: Type, B: A → Type, pair: Pair A B) → getter_ret_ty`
            let getter_ty = getter_ret_ty
                .clone()
                .with_fn_ty_params(getter_params.clone());

            let match_cod_par_id = Ulid::new();

            let cons_args: Vec<_> = struct_def_fields
                .iter()
                .cloned()
                .map(|_| (Ident::blank(), Ulid::new()))
                .collect();

            println!(
                "struct_def_fields.len for {}.{field_name}: {}",
                struct_path,
                struct_def_fields.len(),
            );

            let getter_body = getter_final_param.clone().to_var().matched(
                [(Ident::blank(), match_cod_par_id)],
                getter_ret_ty.with_substitution(
                    getter_final_param.id,
                    desugared::Expr::var(match_cod_par_id, Ident::blank()),
                ),
                [desugared::Arm {
                    constructor: make_ident.clone(),
                    cons_args: cons_args.clone(),
                    body: desugared::Expr::var(cons_args[field_idx].1, Ident::blank()),
                }],
            );

            println!("desugar_struct: getter_body: {getter_body}");

            let getter_val = getter_body.with_fn_params(getter_params.clone());

            let getter_def = desugared::Item::Def {
                ty: getter_ty,
                val: getter_val,
            };

            ret.push((prepend_struct_path(field_name).clone(), getter_def));
        }

        Ok(ret)
    }

    fn desugar_item(&self, path: &Path, item: &Item) -> Result<Vec<(Path, desugared::Item)>> {
        Ok(match item {
            Item::Def { args, ty, val } => {
                let params_desugared = self.desugar_params(args)?;

                let ty = self
                    .desugar_expr(ty)?
                    .with_fn_ty_params(params_desugared.clone());

                let val_span = val.span();

                let val = self
                    .desugar_expr(val)?
                    .with_fn_params(params_desugared)
                    .with_span(val_span);

                vec![(path.clone(), desugared::Item::Def { ty, val })]
            }
            Item::Struct { params, ty, fields } => self.desugar_struct(path, params, ty, fields)?,
            Item::Axiom { ty } => vec![(
                path.clone(),
                desugared::Item::Axiom {
                    ty: self.desugar_expr(ty)?,
                },
            )],
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                vec![(
                    path.clone(),
                    desugared::Item::Inductive {
                        params: self.desugar_params(params)?,
                        ty: self.desugar_expr(ty)?,
                        constructors: constructors
                            .as_ref()
                            .expect("error nodes should not make it to desugaring")
                            .iter()
                            .map(|(name, ty)| self.desugar_expr(ty).map(|ty| (name.clone(), ty)))
                            .collect::<Result<_>>()?,
                    },
                )]
            }
        })
    }

    fn desugar_param(&self, par: &Param) -> Result<Vec<desugared::Param>> {
        let ty = self.desugar_expr(&par.ty)?;

        Ok(par
            .names
            .iter()
            .map(|name| {
                let span = name.span.clone();
                desugared::Param {
                    name: name.clone(),
                    ty: ty.clone(),
                    span,
                }
            })
            .collect())
    }

    fn desugar_params(&self, Params(params): &Params) -> Result<Vec<BindingParam>> {
        Ok(params
            .into_iter()
            .map(|par| self.desugar_param(par))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .map(desugared::Param::binding)
            .collect())
    }

    pub fn desugared_module(&self) -> Result<desugared::Module> {
        // TODO: should this be put anywhere else? seems to be doing its job fine here
        self.module.check_paths()?;

        let mut desugared_items = IndexMap::new();

        for (path, item) in &self.module.items {
            desugared_items.extend(self.desugar_item(path, item)?);
        }

        Ok(desugared::Module {
            submodules: self.module.submodules.clone(),
            items: desugared_items,
        })
    }
}

impl Module {
    fn get_param_names(&self, path: &Path) -> Result<Vec<&Ident>> {
        match self.items.get(path) {
            Some(Item::Def { args: params, .. } | Item::Inductive { params, .. }) => {
                Ok(params.names().collect())
            }
            None => {
                match self.items.get(&path.clone().parent()) {
                    Some(Item::Inductive {
                        constructors,
                        params: ind_def_pars,
                        ..
                    }) => {
                        if let Some((_cons_name, cons_ty)) = constructors
                            .as_ref()
                            .expect("error node made it to desugaring")
                            .iter()
                            .find(|(cons_name, _cons_ty)| cons_name == path.last_component())
                            && let Expr::FnType {
                                params: cons_pars, ..
                            } = cons_ty
                        {
                            return Ok(ind_def_pars.names().chain(cons_pars.names()).collect());
                        }
                    }
                    Some(Item::Struct { fields, params, .. })
                        if path.last_component().name == "make" =>
                    {
                        let fields_params = fields
                            .as_ref()
                            .expect("error node made it to desugaring")
                            .iter()
                            .map(|(name, _ty)| name);

                        return Ok(params.names().chain(fields_params).collect());
                    }
                    _ => (),
                }

                bail!(path.span(), "item `{path}` not found"; @note "while getting argument names");
            }
            _ => bail!(path.span(), "`{path}` does not have named parameters"),
        }
    }

    pub fn check_paths(&self) -> Result<()> {
        for (path, _item) in &self.items {
            if let Some(bad_component) = path
                .components
                .iter()
                .find(|c| FORBIDDEN_NAMES.contains(&c.name.as_str()))
            {
                bail!(
                    bad_component.span.clone(),
                    "`{bad_component}` is a reserved identifier"
                )
            }
        }

        Ok(())
    }

    pub fn load_from_file(
        path: &std::path::Path,
        files: &mut SimpleFiles<String, &str>,
    ) -> anyhow::Result<Self> {
        let src: &str = std::fs::read_to_string(path)?.leak();

        let file_id = files.add(path.to_string_lossy().into_owned(), src);

        let (module, errs) = Self::parse_final(file_id).parse_recovery(src);

        if !errs.is_empty() {
            err::emit_parse_err(errs, file_id, &files);

            anyhow::bail!("failed to parse module at {path:?}");
        };

        let module = module.expect("errorless parsing should be successful");

        Ok(module)
    }

    pub fn load_from_path(
        file_path: &std::path::Path,
        files: &mut SimpleFiles<String, &str>,
    ) -> anyhow::Result<Self> {
        if !file_path.is_file() {
            if file_path.is_dir() {
                anyhow::bail!("file {file_path:?} exists but is not a file");
            } else {
                anyhow::bail!("file {file_path:?} does not exist");
            }
        }

        if !file_path.extension().is_some_and(|s| s == "kwed") {
            anyhow::bail!(
                "canont load file {file_path:?} as it does not have the extension `.kwed`"
            )
        }

        return Self::load_from_file(&file_path, files);
    }

    pub fn desugared(self, self_name: &Ident) -> Result<desugared::Module> {
        let desugarer = Desugarer {
            module: self,
            module_name: self_name.clone(),
        };

        let res = desugarer.desugared_module()?;
        println!("--- desugared module {self_name}:\n{res}");

        Ok(res)
    }
}
