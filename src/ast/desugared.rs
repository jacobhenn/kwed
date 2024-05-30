use super::{Ident, Path, Span};

use std::{collections::HashSet, fmt::Display, ops::Range, rc::Rc};

use crossterm::style::{Color, Stylize};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    TypeType {
        span: Option<Span>,
    },

    Var {
        id: Uuid,
        name: Ident,
        span: Option<Span>,
    },
    Path {
        path: Path,
        span: Option<Span>,
    },

    Fn {
        param: Rc<BindingParam>,
        body: Rc<Self>,
        span: Option<Span>,
    },
    FnType {
        param: Rc<BindingParam>,
        cod: Rc<Self>,
        span: Option<Span>,
    },
    FnApp {
        func: Rc<Self>,
        arg: Rc<Self>,
        span: Option<Span>,
    },

    Match {
        arg: Rc<Self>,
        cod: Rc<Self>,
        arms: Vec<MatchArm>,
        span: Option<Span>,
    },
    Rec {
        id: Uuid,
        var: Ident,
        span: Option<Span>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BindingParam {
    pub name: Ident,
    pub id: Uuid,
    pub ty: Expr,
}

impl Param {
    pub fn binding(self) -> BindingParam {
        BindingParam {
            name: self.name,
            id: Uuid::new_v4(),
            ty: self.ty,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MatchArm {
    pub constructor: Ident,
    pub args: Vec<(Uuid, Ident)>,
    pub body: Expr,
}

impl Display for MatchArm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ", self.constructor)?;

        for (id, name) in &self.args {
            write!(f, "{} ", name.name.as_str().with(uuid_color(*id)))?;
        }

        write!(f, "=> {}", self.body)?;

        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub enum Item {
    Def {
        ty: Expr,
        val: Expr,
    },
    Axiom {
        ty: Expr,
    },
    // TODO: figure out if `params` is even necessary
    Inductive {
        params: Vec<BindingParam>,
        ty: Expr,
        constructors: Vec<Param>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Module {
    pub items: IndexMap<Path, Item>,
}

pub(crate) fn uuid_color(id: Uuid) -> Color {
    Color::Rgb {
        r: id.as_bytes()[0],
        g: id.as_bytes()[1],
        b: id.as_bytes()[2],
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::TypeType { .. } => write!(f, "Type"),
            Expr::Var { id, name, .. } => write!(f, "{}", name.name.as_str().with(uuid_color(*id))),
            Expr::Path { path, .. } => write!(f, "{path}"),
            Expr::Fn { param, body, .. } => write!(
                f,
                "[{}: {}] {body}",
                param.name.name.as_str().with(uuid_color(param.id)),
                param.ty,
            ),
            Expr::FnType { param, cod, .. } => write!(
                f,
                "({}: {}) → {cod}",
                param.name.name.as_str().with(uuid_color(param.id)),
                param.ty
            ),
            Expr::FnApp { func, arg, .. } => write!(f, "({func}) ({arg})"),
            Expr::Match { arg, cod, arms, .. } => write!(
                f,
                "match {arg} to {cod} {{ {} }}",
                arms.iter()
                    .map(MatchArm::to_string)
                    .intersperse(", ".to_string())
                    .collect::<String>()
            ),
            Expr::Rec { id, var: name, .. } => {
                write!(f, "rec {}", name.name.as_str().with(uuid_color(*id)))
            }
        }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Def { ty, val } => write!(f, "def _: {ty} {{ {val} }}"),
            Item::Axiom { ty } => write!(f, "axiom _: {ty}"),
            Item::Inductive {
                params,
                ty,
                constructors,
            } => write!(
                f,
                "inductive _({}): {ty} {{ {} }}",
                params
                    .into_iter()
                    .map(|par| format!(
                        "{}: {}",
                        par.name.name.as_str().with(uuid_color(par.id)),
                        ty
                    ))
                    .intersperse(", ".to_string())
                    .collect::<String>(),
                constructors
                    .into_iter()
                    .map(|c| format!("{}: {}", c.name, c.ty))
                    .intersperse(", ".to_string())
                    .collect::<String>(),
            ),
        }
    }
}

impl Expr {
    pub fn head(&self) -> &Self {
        if let Self::FnApp { func, .. } = self {
            func.head()
        } else {
            self
        }
    }

    fn args_impl<'a>(&'a self, args: &mut Vec<&'a Self>) {
        if let Self::FnApp { func, arg, .. } = self {
            args.push(arg);
            func.args_impl(args);
        }
    }

    pub fn args(&self) -> Vec<&Self> {
        let mut res = Vec::new();
        self.args_impl(&mut res);
        res.reverse();
        res
    }

    fn fn_params_impl<'a>(&'a self, params: &mut Vec<&'a BindingParam>) {
        if let Self::Fn { param, body, .. } = self {
            params.push(param);
            body.fn_params_impl(params);
        }
    }

    pub fn fn_params(&self) -> Vec<&BindingParam> {
        let mut res = Vec::new();
        self.fn_params_impl(&mut res);
        res
    }

    pub fn root_body(&self) -> &Self {
        if let Self::Fn { body, .. } = self {
            body.root_body()
        } else {
            self
        }
    }

    fn fn_ty_params_impl<'a>(&'a self, params: &mut Vec<&'a BindingParam>) {
        if let Self::FnType { param, cod, .. } = self {
            params.push(param);
            cod.fn_ty_params_impl(params);
        }
    }

    pub fn fn_ty_params(&self) -> Vec<&BindingParam> {
        let mut res = Vec::new();
        self.fn_ty_params_impl(&mut res);
        res
    }

    pub fn root_cod(&self) -> &Self {
        if let Self::FnType { cod, .. } = self {
            cod.root_cod()
        } else {
            self
        }
    }

    pub fn is_var_with_id(&self, desired_id: Uuid) -> bool {
        match self {
            Self::Var { id, .. } => *id == desired_id,
            _ => false,
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            Expr::TypeType { span } => span.clone(),
            Expr::Var { span, .. } => span.clone(),
            Expr::Path { span, .. } => span.clone(),
            Expr::Fn { span, .. } => span.clone(),
            Expr::FnType { span, .. } => span.clone(),
            Expr::FnApp { span, .. } => span.clone(),
            Expr::Match { span, .. } => span.clone(),
            Expr::Rec { span, .. } => span.clone(),
        }
    }

    fn eq_impl(this: &Self, that: &Self, ctx: &mut HashSet<[Uuid; 2]>) -> bool {
        match (this, that) {
            (Expr::TypeType { .. }, Expr::TypeType { .. }) => true,
            (Expr::Var { id: lid, .. }, Expr::Var { id: rid, .. }) => {
                lid == rid || ctx.contains(&[*lid, *rid])
            }
            (Expr::Path { path: lpath, .. }, Expr::Path { path: rpath, .. }) => lpath == rpath,
            (
                Expr::Fn {
                    param: lparam,
                    body: lbody,
                    ..
                },
                Expr::Fn {
                    param: rparam,
                    body: rbody,
                    ..
                },
            ) => {
                let params_eq = Self::eq_impl(&lparam.ty, &rparam.ty, ctx);

                ctx.insert([lparam.id, rparam.id]);
                let bodies_eq = Self::eq_impl(lbody, rbody, ctx);
                ctx.remove(&[lparam.id, rparam.id]);

                params_eq && bodies_eq
            }
            (
                Expr::FnType {
                    param: lparam,
                    cod: lcod,
                    ..
                },
                Expr::FnType {
                    param: rparam,
                    cod: rcod,
                    ..
                },
            ) => {
                let params_eq = Self::eq_impl(&lparam.ty, &rparam.ty, ctx);

                ctx.insert([lparam.id, rparam.id]);
                let cods_eq = Self::eq_impl(lcod, rcod, ctx);
                ctx.remove(&[lparam.id, rparam.id]);

                params_eq && cods_eq
            }
            (
                Expr::FnApp {
                    func: lfunc,
                    arg: larg,
                    ..
                },
                Expr::FnApp {
                    func: rfunc,
                    arg: rarg,
                    ..
                },
            ) => Self::eq_impl(lfunc, rfunc, ctx) && Self::eq_impl(larg, rarg, ctx),
            (_, _) => false,
        }
    }

    pub fn eq_up_to_vars(this: &Self, that: &Self) -> bool {
        Self::eq_impl(this, that, &mut HashSet::new())
    }
}

impl Module {
    pub fn new() -> Self {
        Self {
            items: IndexMap::new(),
        }
    }
}
