use crate::{bail, err, err::Result};

use super::{
    desugared::{self, BindingParam},
    Directives, Ident, Path, Span,
};

use std::{collections::HashMap, iter, rc::Rc};

use chumsky::Parser;
use codespan_reporting::files::SimpleFiles;
use indexmap::IndexMap;

use tracing::{debug, instrument};
use uuid::Uuid;

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
                .with_fn_params(params.desugared(not, mod_name)?),
            Expr::FnApp { func, args, .. } => func.desugared(not, mod_name)?.with_args(
                args.into_iter()
                    .map(|arg| arg.desugared(not, mod_name))
                    .collect::<Result<Vec<_>>>()?,
            ),
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
    path: Path,
    not: &HashMap<String, Expr>,
    mod_name: &Ident,
    params: Params,
    ty: Expr,
    fields: Option<Vec<(Ident, Expr)>>,
) -> Result<Vec<(Path, desugared::Item)>> {
    todo!()
    /* let fields = fields.expect("error nodes should not make it to desugaring");

    let make_params = fields
        .iter()
        .cloned()
        .map(|(name, ty)| {
            ty.desugared(not, mod_name)
                .map(|ty| BindingParam::new(name, ty))
        })
        .collect::<Result<Vec<_>>>()?;

    let desugared_params: Vec<BindingParam> = params.desugared(not, mod_name)?;

    let make_ty = path
        .clone()
        .to_expr()
        .with_args(desugared_params.iter().cloned().map(BindingParam::to_var));

    let ind_def = desugared::Item::Inductive {
        params: desugared_params.clone(),
        ty: ty.desugared(not, mod_name)?,
        constructors: vec![(Ident::from_str("make"), make_ty)],
    };

    let mut ret = vec![(path, ind_def)];

    let mut getter_params = desugared_params;
    let getter_final_param_id = Uuid::new_v4();
    getter_params.push(
        BindingParam::blank(
            path.clone()
                .to_expr()
                .with_args(getter_params.iter().cloned().map(BindingParam::to_var)),
        )
        .with_id(getter_final_param_id),
    );

    let elim_cod = make_ty.with_fn_params(desugared_params.iter().cloned());

    for (field_name, field_ty) in fields {
        let getter_path = path.with_suffix(field_name);

        let getter_ty = field_ty
            .desugared(not, mod_name)?
            .with_fn_ty_params(getter_params.iter().cloned());

        let getter_body = path
            .with_suffix(Ident::from_str("elim"))
            .to_expr()
            .with_args(getter_params.iter().cloned().map(BindingParam::to_var))
            .with_arg();
        let getter_val = getter_body.with_fn_params(getter_params.iter().cloned());

        let getter_def = desugared::Item::Def {
            ty: getter_ty,
            val: getter_val,
        };

        ret.push((getter_path, getter_def));
    }

    Ok(ret) */
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

                let val = val
                    .desugared(not, mod_name)?
                    .with_fn_params(params_desugared);

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

    #[instrument(level = "debug", skip(files))]
    pub fn load_from_file(
        path: &std::path::Path,
        files: &mut SimpleFiles<String, &str>,
    ) -> anyhow::Result<Self> {
        let src: &str = std::fs::read_to_string(path)?.leak();

        let file_id = files.add(path.to_string_lossy().into_owned(), src);

        let (module, errs) = Self::parse_final(file_id).parse_recovery(src);

        if !errs.is_empty() {
            debug!("recovered AST: {module:#?}");

            err::emit_parse_err(errs, file_id, &files);

            anyhow::bail!("failed to parse module at {path:?}");
        };

        let module = module.expect("errorless parsing should be successful");

        debug!("parsed module: {module:#?}");

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
