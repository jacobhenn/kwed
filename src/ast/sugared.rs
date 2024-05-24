use super::{desugared, Ident, Path, Span};

use std::{fmt::Display, rc::Rc};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    TypeType,

    Path(Path),

    Fn {
        param: Rc<Param>,
        body: Rc<Self>,
    },
    FnType {
        param: Rc<Param>,
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
        arms: Vec<MatchArm>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Expr,
}

#[derive(Debug, PartialEq, Clone)]
pub struct MatchArm {
    pub constructor: Path,
    pub args: Vec<Ident>,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub enum Item {
    Def {
        args: Vec<Param>,
        ty: Expr,
        val: Expr,
    },
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub items: IndexMap<Path, Item>,
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Expr {
    fn desugared(self) -> desugared::Expr {
        match self {
            Expr::TypeType => desugared::Expr::TypeType,
            Expr::Path(path) => desugared::Expr::Path(path),
            Expr::Fn { param, body } => desugared::Expr::Fn {
                param: Rc::new(Rc::unwrap_or_clone(param).desugared()),
                id: Uuid::new_v4(),
                body: Rc::new(Rc::unwrap_or_clone(body).desugared()),
            },
            Expr::FnType { param, cod } => desugared::Expr::FnType {
                param: Rc::new(Rc::unwrap_or_clone(param).desugared()),
                id: Uuid::new_v4(),
                cod: Rc::new(Rc::unwrap_or_clone(cod).desugared()),
            },
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
                arms: arms.into_iter().map(MatchArm::desugared).collect(),
            },
        }
    }
}

impl Param {
    fn desugared(self) -> desugared::Param {
        desugared::Param {
            name: self.name,
            ty: self.ty.desugared(),
        }
    }
}

impl MatchArm {
    fn desugared(self) -> desugared::MatchArm {
        desugared::MatchArm {
            constructor: self.constructor,
            args: self.args,
            body: self.body.desugared(),
        }
    }
}

impl Item {
    fn desugared(self) -> desugared::Item {
        match self {
            Item::Def { args, ty, val } => {
                let ty = args
                    .iter()
                    .rfold(ty.desugared(), |acc, param| desugared::Expr::FnType {
                        param: Rc::new(param.clone().desugared()),
                        id: Uuid::new_v4(),
                        cod: Rc::new(acc),
                    });

                let val =
                    args.into_iter()
                        .rfold(val.desugared(), |acc, param| desugared::Expr::Fn {
                            param: Rc::new(param.desugared()),
                            id: Uuid::new_v4(),
                            body: Rc::new(acc),
                        });

                desugared::Item::Def { ty, val }
            }
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
