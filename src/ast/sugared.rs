use super::{desugared, Ident, Path, Span};

use std::{ops::Range, rc::Rc};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// An error node representing an expression which failed to parse.
    Error,

    TypeType {
        span: Range<usize>,
    },

    Path {
        path: Path,
        span: Range<usize>,
    },

    Fn {
        params: Params,
        body: Box<Self>,
        span: Range<usize>,
    },
    FnType {
        params: Params,
        cod: Box<Self>,
        span: Range<usize>,
    },
    FnApp {
        func: Box<Self>,
        args: Vec<Self>,
        span: Range<usize>,
    },

    Match {
        arg: Box<Self>,
        cod: Box<Self>,
        arms: Option<Vec<MatchArm>>,
        span: Range<usize>,
    },
    Rec {
        var: Ident,
        span: Range<usize>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub names: Vec<Ident>,
    pub ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Params(pub Vec<Param>);

#[derive(Debug, PartialEq, Clone)]
pub struct MatchArm {
    pub constructor: Ident,
    pub args: Vec<Ident>,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub enum Item {
    Def { args: Params, ty: Expr, val: Expr },
    Axiom { ty: Expr },
    Inductive { ty: Expr, constructors: Params },
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub items: IndexMap<Path, Item>,
}

impl Expr {
    fn desugared(self, file_id: usize) -> desugared::Expr {
        match self {
            Expr::Error => panic!("Error node made it through to desugaring"),
            Expr::TypeType { span } => desugared::Expr::TypeType {
                span: Some(Span::new(file_id, span)),
            },
            Expr::Path { path, span } => desugared::Expr::Path {
                path,
                span: Some(Span::new(file_id, span)),
            },
            Expr::Fn {
                params: Params(params),
                body,
                span,
            } => {
                let body = Rc::new(body.desugared(file_id));

                params
                    .into_iter()
                    .map(|par| par.desugared(file_id))
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(body), |acc, param| {
                        desugared::Expr::Fn {
                            param: Rc::new(param),
                            body: Rc::new(acc),
                            span: Some(Span::new(file_id, span.clone())),
                        }
                    })
            }
            Expr::FnType {
                params: Params(params),
                cod,
                span,
            } => {
                let cod = Rc::new(cod.desugared(file_id));

                params
                    .into_iter()
                    .map(|par| par.desugared(file_id))
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(cod), |acc, param| {
                        desugared::Expr::FnType {
                            param: Rc::new(param),
                            cod: Rc::new(acc),
                            span: Some(Span::new(file_id, span.clone())),
                        }
                    })
            }
            Expr::FnApp { func, args, span } => {
                args.into_iter()
                    .fold(func.desugared(file_id), |acc, arg| desugared::Expr::FnApp {
                        func: Rc::new(acc),
                        arg: Rc::new(arg.desugared(file_id)),
                        span: Some(Span::new(file_id, span.clone())),
                    })
            }
            Expr::Match {
                arg,
                cod,
                arms,
                span,
            } => desugared::Expr::Match {
                arg: Rc::new(arg.desugared(file_id)),
                cod: Rc::new(cod.desugared(file_id)),
                arms: arms
                    .expect("error nodes should not make it to desugaring")
                    .into_iter()
                    .map(|arm| arm.desugared(file_id))
                    .collect(),
                span: Some(Span::new(file_id, span)),
            },
            Expr::Rec { var, span } => desugared::Expr::Rec {
                var,
                id: Uuid::new_v4(),
                span: Some(Span::new(file_id, span)),
            },
        }
    }
}

impl Param {
    fn desugared(self, file_id: usize) -> Vec<desugared::Param> {
        let ty = self.ty.desugared(file_id);

        self.names
            .into_iter()
            .map(|name| desugared::Param {
                name,
                ty: ty.clone(),
            })
            .collect()
    }
}

impl MatchArm {
    fn desugared(self, file_id: usize) -> desugared::MatchArm {
        desugared::MatchArm {
            constructor: self.constructor,
            args: self
                .args
                .into_iter()
                .map(|arg| (Uuid::new_v4(), arg))
                .collect(),
            body: self.body.desugared(file_id),
        }
    }
}

impl Item {
    fn desugared(self, file_id: usize) -> desugared::Item {
        match self {
            Item::Def {
                args: Params(params),
                ty,
                val,
            } => {
                let ty = params
                    .iter()
                    .cloned()
                    .map(|par| par.desugared(file_id))
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(ty.desugared(file_id), |acc, param| {
                        desugared::Expr::FnType {
                            param: Rc::new(param),
                            cod: Rc::new(acc),
                            span: None,
                        }
                    });

                let val = params
                    .into_iter()
                    .map(|par| par.desugared(file_id))
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(val.desugared(file_id), |acc, param| desugared::Expr::Fn {
                        param: Rc::new(param),
                        body: Rc::new(acc),
                        span: None,
                    });

                desugared::Item::Def { ty, val }
            }
            Item::Axiom { ty } => desugared::Item::Axiom {
                ty: ty.desugared(file_id),
            },
            Item::Inductive {
                ty,
                constructors: Params(constructors),
            } => desugared::Item::Inductive {
                ty: ty.desugared(file_id),
                constructors: constructors
                    .into_iter()
                    .map(|par| par.desugared(file_id))
                    .flatten()
                    .collect(),
            },
        }
    }
}

impl Module {
    pub fn desugared(self, file_id: usize) -> desugared::Module {
        desugared::Module {
            items: self
                .items
                .into_iter()
                .map(|(path, item)| (path, item.desugared(file_id)))
                .collect(),
        }
    }
}
