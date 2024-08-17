use super::{Ident, Path, Span};

use std::{collections::HashSet, fmt::Display, rc::Rc};

use crossterm::style::{Color, Stylize};

use indexmap::IndexMap;

use uuid::Uuid;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    TypeType {
        span: Option<Span>,
    },

    // TODO: `Var` and `Path` may not need to store a span, since they are already stored in their
    // contents.
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

impl BindingParam {
    pub fn new(name: Ident, ty: Expr) -> Self {
        Self {
            name,
            id: Uuid::new_v4(),
            ty,
        }
    }

    pub fn blank(ty: Expr) -> Self {
        let id = Uuid::new_v4();

        Self {
            name: Ident::from_id(id),
            id,
            ty,
        }
    }

    pub fn to_var(self) -> Expr {
        Expr::var(self.id, self.name.clone(), None)
    }
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
        constructors: Vec<(Ident, Expr)>,
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
            Expr::Var { id, name, .. } => {
                write!(f, "{}", name.name.as_str().with(uuid_color(*id)),)
            }
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
            Expr::FnApp { .. } => {
                self.head().fmt_in_parens(f)?;

                for arg in self.args() {
                    write!(f, " ")?;
                    arg.fmt_in_parens(f)?;
                }

                Ok(())
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
                    .map(|c| format!("{}: {}", c.name, c.ty))
                    .intersperse(", ".to_string())
                    .collect::<String>(),
                constructors
                    .into_iter()
                    .map(|(name, ty)| format!("{name}: {ty}"))
                    .intersperse(", ".to_string())
                    .collect::<String>(),
            ),
        }
    }
}

impl Expr {
    pub fn type_type(span: Option<Span>) -> Self {
        Self::TypeType { span }
    }

    pub fn var(id: Uuid, name: Ident, span: Option<Span>) -> Self {
        Self::Var { id, name, span }
    }

    pub fn path(path: Path, span: Option<Span>) -> Self {
        Self::Path { path, span }
    }

    pub fn func(param: BindingParam, body: Expr, span: Option<Span>) -> Self {
        Self::Fn {
            param: Rc::new(param),
            body: Rc::new(body),
            span,
        }
    }

    pub fn fn_type(param: BindingParam, cod: Expr, span: Option<Span>) -> Self {
        Self::FnType {
            param: Rc::new(param),
            cod: Rc::new(cod),
            span,
        }
    }

    pub fn fn_app(func: Expr, arg: Expr, span: Option<Span>) -> Self {
        Self::FnApp {
            func: Rc::new(func),
            arg: Rc::new(arg),
            span,
        }
    }

    pub fn is_atomic(&self) -> bool {
        match self {
            Self::TypeType { .. } | Self::Var { .. } | Self::Path { .. } => true,
            Self::Fn { .. } | Self::FnType { .. } | Self::FnApp { .. } => false,
        }
    }

    fn fmt_in_parens(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_atomic() {
            write!(f, "{self}")
        } else {
            write!(f, "({self})")
        }
    }

    // TODO: rewrite all of these to return iterators instead of vecs

    /// Returns the head of a function application.
    /// ```
    /// f x y
    /// ^
    /// head
    /// ```
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

    /// Returns the arguments of a function application.
    /// ```
    /// f x y
    ///   ^^^
    ///   args
    /// ```
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

    /// Returns the parameters of a function
    /// ```
    /// [x: A] [y: B] z
    /// ^^^^^^^^^^^^^
    /// parameters
    /// ```
    pub fn fn_params(&self) -> Vec<&BindingParam> {
        let mut res = Vec::new();
        self.fn_params_impl(&mut res);
        res
    }

    /// Returns the body of a (possibly nested) function
    /// ```
    /// [x: A] [y: B] z
    ///               ^
    ///               body
    /// ```
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

    /// Returns the parameters of a function type
    /// ```
    /// (x: A) → (y: B) → C
    /// ^^^^^^^^^^^^^^^
    /// parameters
    /// ```
    pub fn fn_ty_params(&self) -> Vec<&BindingParam> {
        let mut res = Vec::new();
        self.fn_ty_params_impl(&mut res);
        res
    }

    /// Returns the codomain of a (possibly nested) function type
    /// ```
    /// (x: A) → (y: B) → C
    ///                   ^
    ///                   codomain
    /// ```
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

    pub fn is_path_to(&self, desired_path: &Path) -> bool {
        match self {
            Self::Path { path, .. } => path == desired_path,
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
