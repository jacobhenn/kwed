use crate::{bail, err::Result};

use super::{desugared, Directives, Ident, Path, Span};

use std::{collections::HashMap, iter, ops::Range, rc::Rc};

use indexmap::IndexMap;

use tracing::debug;
use uuid::Uuid;

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
    Axiom {
        ty: Expr,
    },
    Inductive {
        params: Params,
        ty: Expr,
        constructors: Option<Vec<(Ident, Expr)>>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub directives: Directives,
    pub notation: HashMap<String, Expr>,
    pub items: IndexMap<Path, Item>,
}

impl Expr {
    fn span_mut(&mut self) -> &mut Span {
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

    fn desugared(self, not: &HashMap<String, Expr>) -> Result<desugared::Expr> {
        Ok(match self {
            Expr::Error => panic!("Error node made it through to desugaring"),
            Expr::TypeType { level, span } => desugared::Expr::TypeType {
                level,
                span: Some(span),
            },
            Expr::Displace { amount, arg, span } => desugared::Expr::Displace {
                amount,
                arg: Rc::new(arg.desugared(not)?),
                span: Some(span),
            },
            Expr::Path { path, span } => desugared::Expr::Path {
                path,
                span: Some(span),
            },
            Expr::Fn {
                params: Params(params),
                body,
                span,
            } => {
                let body = Rc::new(body.desugared(not)?);

                params
                    .into_iter()
                    .map(|par| par.desugared(not))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(body), |acc, param| {
                        desugared::Expr::func(param, acc, Some(span.clone()))
                    })
            }
            Expr::FnType {
                params: Params(params),
                cod,
                span,
            } => {
                let cod = Rc::new(cod.desugared(not)?);

                // TODO: it seems like I'm repeating this every time. could I turn it into a
                // method on `Params`?
                params
                    .into_iter()
                    .map(|par| par.desugared(not))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(cod), |acc, param| {
                        desugared::Expr::fn_type(param, acc, Some(span.clone()))
                    })
            }
            Expr::FnApp { func, args, span } => {
                args.into_iter().fold(func.desugared(not), |acc, arg| {
                    acc.and_then(|acc| {
                        arg.desugared(not)
                            .map(|arg| desugared::Expr::fn_app(acc, arg, Some(span.clone())))
                    })
                })?
            }
            Expr::Number { number, span } => {
                let Some(mut number_0) = not.get("number_0").cloned() else {
                    bail!(Some(span), "notation `number_0` not set");
                };

                let Some(mut number_suc) = not.get("number_suc").cloned() else {
                    bail!(Some(span), "notation `number_suc` not set");
                };

                *number_0.span_mut() = span.clone();
                *number_suc.span_mut() = span.clone();

                if let Ok(n) = usize::try_from(number) {
                    let res = iter::repeat_n(number_suc.desugared(&HashMap::new())?, n)
                        .rfold(number_0.desugared(&HashMap::new())?, |acc, f| {
                            desugared::Expr::fn_app(f, acc, Some(span.clone()))
                        });

                    res
                } else {
                    bail!(Some(span), "negative number literals are not yet supported")
                }
            }
        })
    }
}

impl Item {
    fn desugared(self, not: &HashMap<String, Expr>) -> Result<desugared::Item> {
        Ok(match self {
            Item::Def {
                args: Params(params),
                ty,
                val,
            } => {
                let ty = params
                    .iter()
                    .cloned()
                    .map(|par| par.desugared(not))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(ty.desugared(not)?, |acc, param| {
                        desugared::Expr::fn_type(param, acc, None)
                    });

                let val = params
                    .into_iter()
                    .map(|par| par.desugared(not))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(val.desugared(not)?, |acc, param| {
                        desugared::Expr::func(param, acc, None)
                    });

                desugared::Item::Def { ty, val }
            }
            Item::Axiom { ty } => desugared::Item::Axiom {
                ty: ty.desugared(not)?,
            },
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                let desugared_params: Vec<desugared::BindingParam> = params
                    .0
                    .into_iter()
                    .map(|param| param.desugared(not))
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .flatten()
                    .map(desugared::Param::binding)
                    .collect();

                desugared::Item::Inductive {
                    params: desugared_params.clone(),
                    ty: ty.desugared(not)?,
                    constructors: constructors
                        .expect("error nodes should not make it to desugaring")
                        .into_iter()
                        .map(|(name, ty)| ty.desugared(not).map(|ty| (name, ty)))
                        .collect::<Result<_>>()?,
                }
            }
        })
    }
}

impl Param {
    fn desugared(self, not: &HashMap<String, Expr>) -> Result<Vec<desugared::Param>> {
        let ty = self.ty.desugared(not)?;

        Ok(self
            .names
            .into_iter()
            .map(|name| desugared::Param {
                name,
                ty: ty.clone(),
            })
            .collect())
    }
}

impl Module {
    pub fn desugared(self) -> Result<desugared::Module> {
        let items: IndexMap<Path, desugared::Item> = self
            .items
            .into_iter()
            .map(|(path, item)| item.desugared(&self.notation).map(|it| (path, it)))
            .collect::<Result<_>>()?;

        Ok(desugared::Module {
            directives: self.directives,
            items,
        })
    }
}
