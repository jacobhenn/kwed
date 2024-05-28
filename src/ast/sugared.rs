use super::{desugared, Ident, Path};

use std::rc::Rc;

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// An error node representing an expression which failed to parse.
    Error,

    TypeType,

    Path(Path),

    Fn {
        params: Params,
        body: Rc<Self>,
    },
    FnType {
        params: Params,
        cod: Rc<Self>,
    },
    FnApp {
        func: Rc<Self>,
        arg: Rc<Self>,
    },

    Eq {
        lhs: Rc<Self>,
        rhs: Rc<Self>,
    },
    Refl(Rc<Self>),

    Match {
        arg: Rc<Self>,
        cod: Rc<Self>,
        arms: Option<Vec<MatchArm>>,
    },
    Rec(Ident),
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
        constructors: Params,
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
            Expr::TypeType => desugared::Expr::TypeType,
            Expr::Path(path) => desugared::Expr::Path(path),
            Expr::Fn {
                params: Params(params),
                body,
            } => {
                let body = Rc::new(Rc::unwrap_or_clone(body).desugared());

                params
                    .into_iter()
                    .map(Param::desugared)
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(body), |acc, param| {
                        desugared::Expr::Fn {
                            param: Rc::new(param),
                            body: Rc::new(acc),
                        }
                    })
            }
            Expr::FnType {
                params: Params(params),
                cod,
            } => {
                let cod = Rc::new(Rc::unwrap_or_clone(cod).desugared());

                params
                    .into_iter()
                    .map(Param::desugared)
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(Rc::unwrap_or_clone(cod), |acc, param| {
                        desugared::Expr::FnType {
                            param: Rc::new(param),
                            cod: Rc::new(acc),
                        }
                    })
            }
            Expr::FnApp { func, arg } => desugared::Expr::FnApp {
                func: Rc::new(Rc::unwrap_or_clone(func).desugared()),
                arg: Rc::new(Rc::unwrap_or_clone(arg).desugared()),
            },
            Expr::Eq { lhs, rhs } => desugared::Expr::Eq {
                lhs: Rc::new(Rc::unwrap_or_clone(lhs).desugared()),
                rhs: Rc::new(Rc::unwrap_or_clone(rhs).desugared()),
            },
            Expr::Refl(arg) => desugared::Expr::Refl(Rc::new(Rc::unwrap_or_clone(arg).desugared())),
            Expr::Match { arg, cod, arms } => desugared::Expr::Match {
                arg: Rc::new(Rc::unwrap_or_clone(arg).desugared()),
                cod: Rc::new(Rc::unwrap_or_clone(cod).desugared()),
                arms: arms
                    .expect("error nodes should not make it to desugaring")
                    .into_iter()
                    .map(MatchArm::desugared)
                    .collect(),
            },
            Expr::Rec(name) => desugared::Expr::Rec {
                name,
                id: Uuid::new_v4(),
            },
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

impl MatchArm {
    fn desugared(self) -> desugared::MatchArm {
        desugared::MatchArm {
            constructor: self.constructor,
            args: self
                .args
                .into_iter()
                .map(|arg| (Uuid::new_v4(), arg))
                .collect(),
            body: self.body.desugared(),
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
                    .rfold(ty.desugared(), |acc, param| desugared::Expr::FnType {
                        param: Rc::new(param),
                        cod: Rc::new(acc),
                    });

                let val = params
                    .into_iter()
                    .map(Param::desugared)
                    .flatten()
                    .map(desugared::Param::binding)
                    .rfold(val.desugared(), |acc, param| desugared::Expr::Fn {
                        param: Rc::new(param),
                        body: Rc::new(acc),
                    });

                desugared::Item::Def { ty, val }
            }
            Item::Axiom { ty } => desugared::Item::Axiom { ty: ty.desugared() },
            Item::Inductive {
                params: Params(params),
                ty,
                constructors: Params(constructors),
            } => desugared::Item::Inductive {
                params: params
                    .into_iter()
                    .map(Param::desugared)
                    .flatten()
                    .map(desugared::Param::binding)
                    .collect(),
                ty: ty.desugared(),
                constructors: constructors
                    .into_iter()
                    .map(Param::desugared)
                    .flatten()
                    .collect(),
            },
        }
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
