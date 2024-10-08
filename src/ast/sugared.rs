use crate::{bail, err, err::Result};

use super::{
    desugared::{self, BindingParam},
    Directives, Ident, Path, Span,
};

use std::{collections::HashMap, iter, rc::Rc};

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

    Displace {
        amount: usize,
        arg: Box<Self>,
        span: Span,
    },

    Path {
        path: Path,
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub names: Vec<Ident>,
    pub ty: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Params(pub Vec<Param>);

#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub constructor: Ident,
    pub cons_args: Vec<Ident>,
    pub body: Expr,
}

impl Arm {
    fn desugared(self, not: &HashMap<String, Expr>, mod_name: &Ident) -> Result<desugared::Arm> {
        Ok(desugared::Arm {
            constructor: self.constructor,
            cons_args: self
                .cons_args
                .into_iter()
                .map(|name| (name, Ulid::new()))
                .collect(),
            body: self.body.desugared(not, mod_name)?,
        })
    }
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
pub struct Module {
    pub directives: Directives,
    pub submodules: Vec<Ident>,
    pub imports: Vec<Path>,
    pub notation: HashMap<String, Expr>,
    pub items: IndexMap<Path, Item>,
}

impl Expr {
    pub(crate) fn span(&self) -> Span {
        match self {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { span, .. }
            | Expr::Displace { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. }
            | Expr::Number { span, .. } => span.clone(),
        }
    }

    pub(crate) fn span_mut(&mut self) -> &mut Span {
        match self {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { span, .. }
            | Expr::Displace { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. }
            | Expr::Number { span, .. } => span,
        }
    }

    // TODO: desugaring is getting a little bloated; it might be a good idea at some point to
    // split this up into phases for module loading, path expansion, etc.
    fn desugared(self, not: &HashMap<String, Expr>, mod_name: &Ident) -> Result<desugared::Expr> {
        Ok(match self {
            Expr::Error => panic!("error node made it to desugaring"),
            Expr::TypeType { level, span } => desugared::Expr::TypeType {
                level,
                span: Some(span),
            },
            Expr::Displace { amount, arg, span } => desugared::Expr::Displace {
                amount,
                arg: Rc::new(arg.desugared(not, mod_name)?),
                span: Some(span),
            },
            Expr::Path { path, span } => desugared::Expr::Path {
                path,
                span: Some(span),
            },
            Expr::Fn { params, body, .. } => body
                .desugared(not, mod_name)?
                .with_fn_params(params.desugared(not, mod_name)?),
            Expr::FnType { params, cod, .. } => cod
                .desugared(not, mod_name)?
                .with_fn_ty_params(params.desugared(not, mod_name)?),
            Expr::FnApp { func, args, .. } => func.desugared(not, mod_name)?.with_args(
                args.into_iter()
                    .map(|arg| arg.desugared(not, mod_name))
                    .collect::<Result<Vec<_>>>()?,
            ),
            Expr::Match {
                arg,
                cod_pars,
                cod_body,
                arms,
                span,
            } => desugared::Expr::Match {
                arg: Rc::new(arg.desugared(not, mod_name)?),
                cod_pars: cod_pars
                    .into_iter()
                    .map(|name| (name, Ulid::new()))
                    .collect(),
                cod_body: Rc::new(cod_body.desugared(not, mod_name)?),
                arms: arms
                    .into_iter()
                    .map(|arm| arm.desugared(not, mod_name))
                    .collect::<Result<_>>()?,
                span: Some(span),
            },
            Expr::Rec { arg_name, span } => desugared::Expr::Rec {
                arg_id: Ulid::nil(),
                arg_name,
                span: Some(span),
            },
            Expr::Number { number, span } => {
                let Some(mut number_0) = not.get("number-0").cloned() else {
                    bail!(Some(span), "notation `number-0` not set");
                };

                let Some(mut number_suc) = not.get("number-suc").cloned() else {
                    bail!(Some(span), "notation `number-suc` not set");
                };

                *number_0.span_mut() = span.clone();
                *number_suc.span_mut() = span.clone();

                match usize::try_from(number) {
                    Ok(n) => iter::repeat_n(number_suc.desugared(&HashMap::new(), mod_name)?, n)
                        .rfold(number_0.desugared(&HashMap::new(), mod_name)?, |acc, f| {
                            f.with_arg(acc).with_span(span.clone())
                        }),
                    Err(e) => {
                        bail!(Some(span), "unsupported number literal: {e}")
                    }
                }
            }
        })
    }
}

fn desugar_struct(
    struct_path: Path,
    not: &HashMap<String, Expr>,
    mod_name: &Ident,
    struct_def_params: Params,
    struct_def_ty: Expr,
    struct_def_fields: Option<Vec<(Ident, Expr)>>,
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
    let fields = struct_def_fields.expect("error nodes should not make it to desugaring");

    // the parameters of the `make` constructor: `(first: A, second: B first)`
    let make_params = fields
        .iter()
        .cloned()
        .map(|(name, ty)| {
            ty.desugared(not, mod_name)
                .map(|ty| BindingParam::new(name, ty))
        })
        .collect::<Result<Vec<_>>>()?;

    let desugared_struct_def_params: Vec<BindingParam> =
        struct_def_params.desugared(not, mod_name)?;

    // the type of the `make` constructor: `(first: A, second: B first) → Pair A B`
    let make_ty = struct_path
        .clone()
        .to_expr()
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
        ty: struct_def_ty.desugared(not, mod_name)?,
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
        BindingParam::blank(struct_path.clone().to_expr().with_args(param_vars.clone()));

    // the parameters of all getters: `A: Type, B: A → Type, pair: Pair A B`
    let getter_params = desugared_struct_def_params
        .iter()
        .cloned()
        .chain([getter_final_param.clone()]);

    let prepend_struct_path = |name: &Ident| struct_path.clone().with_suffix(name.clone());

    for (field_idx, (field_name, field_ty)) in fields.iter().enumerate() {
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

        let desugared_field_ty = field_ty.clone().desugared(not, mod_name)?;

        // the return type of this getter: B (Pair.first A B pair)
        let mut getter_ret_ty = desugared_field_ty.clone();
        for name in fields.iter().map(|(name, _ty)| name) {
            getter_ret_ty.replace(
                &|expr: &desugared::Expr| expr.is_path_to_ident(name),
                &prepend_struct_path(name)
                    .clone()
                    .to_expr()
                    .with_args(param_vars.clone())
                    .with_arg(getter_final_param.clone().to_var()),
            );
        }

        // the type of this getter: `(A: Type, B: A → Type, pair: Pair A B) → getter_ret_ty`
        let getter_ty = getter_ret_ty
            .clone()
            .with_fn_ty_params(getter_params.clone());

        let match_cod_par_id = Ulid::new();

        let cons_args: Vec<_> = desugared_struct_def_params
            .iter()
            .cloned()
            .map(|_| (Ident::blank(), Ulid::new()))
            .collect();

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

impl Item {
    fn desugared(
        self,
        path: Path,
        not: &HashMap<String, Expr>,
        mod_name: &Ident,
    ) -> Result<Vec<(Path, desugared::Item)>> {
        Ok(match self {
            Item::Def { args, ty, val } => {
                let params_desugared = args.desugared(not, mod_name)?;

                let ty = ty
                    .desugared(not, mod_name)?
                    .with_fn_ty_params(params_desugared.clone());

                let val_span = val.span();

                let val = val
                    .desugared(not, mod_name)?
                    .with_fn_params(params_desugared)
                    .with_span(val_span);

                vec![(path, desugared::Item::Def { ty, val })]
            }
            Item::Struct { params, ty, fields } => {
                desugar_struct(path, not, mod_name, params, ty, fields)?
            }
            Item::Axiom { ty } => vec![(
                path,
                desugared::Item::Axiom {
                    ty: ty.desugared(not, mod_name)?,
                },
            )],
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                vec![(
                    path,
                    desugared::Item::Inductive {
                        params: params.desugared(not, mod_name)?,
                        ty: ty.desugared(not, mod_name)?,
                        constructors: constructors
                            .expect("error nodes should not make it to desugaring")
                            .into_iter()
                            .map(|(name, ty)| ty.desugared(not, mod_name).map(|ty| (name, ty)))
                            .collect::<Result<_>>()?,
                    },
                )]
            }
        })
    }
}

impl Param {
    fn desugared(
        self,
        not: &HashMap<String, Expr>,
        mod_name: &Ident,
    ) -> Result<Vec<desugared::Param>> {
        let ty = self.ty.desugared(not, mod_name)?;

        Ok(self
            .names
            .into_iter()
            .map(|name| {
                let span = name.span.clone();
                desugared::Param {
                    name,
                    ty: ty.clone(),
                    span,
                }
            })
            .collect())
    }
}

impl Params {
    fn desugared(self, not: &HashMap<String, Expr>, mod_name: &Ident) -> Result<Vec<BindingParam>> {
        Ok(self
            .0
            .into_iter()
            .map(|par| par.desugared(not, mod_name))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .map(desugared::Param::binding)
            .collect())
    }
}

impl Module {
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

    pub fn desugared(self, mod_name: &Ident) -> Result<desugared::Module> {
        // TODO: should this be put anywhere else? seems to be doing its job fine here
        self.check_paths()?;

        let mut desugared_items = IndexMap::new();

        for (path, item) in self.items {
            desugared_items.extend(item.desugared(path, &self.notation, mod_name)?);
        }

        Ok(desugared::Module {
            directives: self.directives,
            submodules: self.submodules,
            items: desugared_items,
        })
    }
}
