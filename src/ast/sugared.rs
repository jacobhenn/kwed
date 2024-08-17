use super::{desugared, Ident, Path, Span};

use std::{ops::Range, rc::Rc};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// An error node representing an expression which failed to parse.
    Error,

    TypeType {
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
    pub items: IndexMap<Path, Item>,
}

impl Expr {
    fn desugared(self) -> desugared::Expr {
        match self {
            Expr::Error => panic!("Error node made it through to desugaring"),
            Expr::TypeType { span } => desugared::Expr::TypeType { span: Some(span) },
            Expr::Path { path, span } => desugared::Expr::Path {
                path,
                span: Some(span),
            },
            Expr::Fn {
                params: Params(params),
                body,
                span,
            } => {
                let body = Rc::new(body.desugared());

                params
                    .into_iter()
                    .map(|par| par.desugared())
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
                let cod = Rc::new(cod.desugared());

                params
                    .into_iter()
                    .map(|par| par.desugared())
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(cod), |acc, param| {
                        desugared::Expr::fn_type(param, acc, Some(span.clone()))
                    })
            }
            Expr::FnApp { func, args, span } => {
                args.into_iter().fold(func.desugared(), |acc, arg| {
                    desugared::Expr::fn_app(acc, arg.desugared(), Some(span.clone()))
                })
            }
        }
    }
}

impl Item {
    fn desugared(self) -> desugared::Item {
        match self {
            Item::Def {
                args: Params(params),
                ty,
                val,
            } => {
                let ty = params
                    .iter()
                    .cloned()
                    .map(Param::desugared)
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(ty.desugared(), |acc, param| {
                        desugared::Expr::fn_type(param, acc, None)
                    });

                let val = params
                    .into_iter()
                    .map(|par| par.desugared())
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(val.desugared(), |acc, param| {
                        desugared::Expr::func(param, acc, None)
                    });

                desugared::Item::Def { ty, val }
            }
            Item::Axiom { ty } => desugared::Item::Axiom { ty: ty.desugared() },
            Item::Inductive {
                params,
                ty,
                constructors,
            } => {
                let desugared_params: Vec<desugared::BindingParam> = params
                    .0
                    .into_iter()
                    .map(|param| param.desugared())
                    .flatten()
                    .map(desugared::Param::binding)
                    .collect();

                desugared::Item::Inductive {
                    params: desugared_params.clone(),
                    ty: ty.desugared(),
                    constructors: constructors
                        .expect("error nodes should not make it to desugaring")
                        .into_iter()
                        .map(|(name, ty)| (name, ty.desugared()))
                        .collect(),
                }
            }
        }
    }
}

impl Param {
    fn desugared(self) -> Vec<desugared::Param> {
        let ty = self.ty.desugared();

        self.names
            .into_iter()
            .map(|name| desugared::Param {
                name,
                ty: ty.clone(),
            })
            .collect()
    }
}

impl Module {
    pub fn desugared(self) -> desugared::Module {
        desugared::Module {
            items: self
                .items
                .into_iter()
                .map(|(path, item)| (path, item.desugared()))
                .collect(),
        }
    }
}
