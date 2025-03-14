use crate::{ast::sugared, bail, err::Result, log};

use super::{Ident, Path, Span};

use std::{fmt::Display, mem, rc::Rc};

use base64::{engine::general_purpose::STANDARD_NO_PAD, Engine as _};
use codespan_reporting::files::SimpleFiles;
use indexmap::IndexMap;
use yansi::{Color, Paint};

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    TypeType {
        level: usize,
        span: Option<Span>,
    },

    Hole {
        id: u128,
        span: Option<Span>,
    },

    Var {
        id: u128,
        name: Ident,
        span: Option<Span>,
    },
    Path {
        path: Path,
        level: usize,
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
        cod_pars: Vec<(Ident, u128)>,
        cod_body: Rc<Self>,
        arms: Vec<Arm>,
        span: Option<Span>,
    },
    Rec {
        arg_id: u128,
        arg_name: Ident,
        span: Option<Span>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Expr,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BindingParam {
    pub name: Ident,
    pub id: u128,
    pub ty: Expr,
    pub span: Option<Span>,
}

impl BindingParam {
    pub fn new(name: Ident, ty: Expr) -> Self {
        Self { name, id: fastrand::u128(..), ty, span: None }
    }

    pub fn with_id(self, id: u128) -> Self {
        Self { id, ..self }
    }

    pub fn blank(ty: Expr) -> Self {
        let id = fastrand::u128(..);

        Self { name: Ident::blank(), id, ty, span: None }
    }

    pub fn to_var(self) -> Expr {
        Expr::var(self.id, self.name.clone())
    }
}

impl Param {
    pub fn binding(self) -> BindingParam {
        BindingParam { name: self.name, id: fastrand::u128(..), ty: self.ty, span: self.span }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Arm {
    pub constructor: Ident,
    pub cons_args: Vec<(Ident, u128)>,
    pub body: Expr,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Item {
    Def { ty: Expr, val: Expr },
    Axiom { ty: Expr },
    Inductive { params: Vec<BindingParam>, ty: Expr, constructors: Vec<(Ident, Expr)> },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Module {
    pub submodules: Vec<Ident>,
    pub items: IndexMap<Path, Item>,
}

pub(crate) fn id_color(id: u128) -> Color {
    Color::Rgb(id.to_be_bytes()[0], id.to_be_bytes()[1], id.to_be_bytes()[2])
}

pub(crate) fn id_str(id: u128) -> String {
    STANDARD_NO_PAD.encode(id.to_be_bytes())
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::TypeType { level, .. } => write!(f, "Type {level}")?,
            Expr::Hole { id, .. } => {
                write!(f, "{}", format!("_{}", id_str(*id)).paint(id_color(*id).background()))?
            }
            Expr::Var { id, name, .. } => write!(f, "{}", name.name.as_str().paint(id_color(*id)))?,
            // TODO: maybe do something fancy here to write just enough components to disambiguate
            Expr::Path { path, level, .. } => {
                if log::get_config().print_full_paths {
                    write!(f, "{}", path)?
                } else {
                    write!(f, "{}", path.last_component())?
                }

                if *level != 0 {
                    write!(f, "@{level}")?;
                }
            }
            Expr::Fn { param, body, .. } => write!(
                f,
                "[{}: {}] {body}",
                param.name.name.as_str().paint(id_color(param.id)),
                param.ty,
            )?,
            Expr::FnType { param, cod, .. } => {
                let param_name_colored = param.name.name.as_str().paint(id_color(param.id));

                if cod.contains_var(param.id) {
                    write!(f, "({param_name_colored}: {})", param.ty)?;
                } else {
                    param.ty.fmt_in_parens(f)?;
                }

                write!(f, " → {cod}",)?
            }
            Expr::FnApp { .. } => {
                self.head().fmt_in_parens(f)?;

                for arg in self.args() {
                    write!(f, " ")?;
                    arg.fmt_in_parens(f)?;
                }
            }
            Expr::Match { arg, cod_pars, cod_body, arms, .. } => write!(
                f,
                "match {arg} to [{}] {cod_body} {{ {} }}",
                cod_pars
                    .iter()
                    .map(|(name, id)| name.name.as_str().paint(id_color(*id)).to_string())
                    .intersperse(" ".to_string())
                    .collect::<String>(),
                arms.iter().map(Arm::to_string).intersperse(", ".to_string()).collect::<String>(),
            )?,
            Expr::Rec { arg_id, arg_name, .. } => {
                write!(f, "rec {}", arg_name.name.as_str().paint(id_color(*arg_id)))?
            }
        };

        if self.is_atomic() && std::env::var("KW_PRINT_SPANS").is_ok_and(|s| s == "true") {
            if let Some(span) = self.span() {
                write!(f, "<{}>", span)?;
            } else {
                write!(f, "<?>")?;
            }
        }

        Ok(())
    }
}

impl Display for Arm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} => {}",
            self.constructor,
            self.cons_args
                .iter()
                .map(|(name, id)| name.name.as_str().paint(id_color(*id)).to_string())
                .intersperse(" ".to_string())
                .collect::<String>(),
            self.body,
        )
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty,)
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Def { ty, val, .. } => write!(f, "def: {ty} {{ {val} }}"),
            Item::Axiom { ty, .. } => write!(f, "axiom: {ty}"),
            Item::Inductive { params, ty, constructors, .. } => write!(
                f,
                "inductive({}): {ty} {{ {} }}",
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

impl Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "mod {{")?;
        for (path, item) in &self.items {
            writeln!(f, "item {path} :: {item}")?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Expr {
    pub fn rc(self) -> Rc<Self> {
        Rc::new(self)
    }

    pub fn var(id: u128, name: Ident) -> Self {
        Self::Var { id, name, span: None }
    }

    pub fn with_fn_param(self, param: BindingParam) -> Self {
        Self::Fn { param: Rc::new(param), body: Rc::new(self), span: None }
    }

    pub fn with_fn_ty_param(self, param: BindingParam) -> Self {
        Self::FnType { param: Rc::new(param), cod: Rc::new(self), span: None }
    }

    pub fn with_arg(self, arg: Expr) -> Self {
        Self::FnApp { func: Rc::new(self), arg: Rc::new(arg), span: None }
    }

    pub fn with_span(mut self, span: Span) -> Self {
        *self.span_mut() = Some(span);
        self
    }

    pub fn with_span_opt(mut self, span: Option<Span>) -> Self {
        *self.span_mut() = span;
        self
    }

    pub fn with_args(self, args: impl IntoIterator<Item = Self>) -> Self {
        let self_span = self.span();

        args.into_iter().fold(self, |acc, arg| {
            let arg_span = arg.span().clone();
            acc.with_arg(arg).with_span_opt(Span::hull_opts(self_span.clone(), arg_span))
        })
    }

    pub fn with_fn_params<I>(self, params: I) -> Self
    where
        I: IntoIterator<Item = BindingParam, IntoIter: DoubleEndedIterator>,
    {
        let self_span = self.span();

        params.into_iter().rfold(self, |acc, par| {
            let par_span = par.span.clone();
            acc.with_fn_param(par).with_span_opt(Span::hull_opts(par_span, self_span.clone()))
        })
    }

    pub fn with_fn_ty_params<I>(self, params: I) -> Self
    where
        I: IntoIterator<Item = BindingParam, IntoIter: DoubleEndedIterator>,
    {
        let self_span = self.span();

        params.into_iter().rfold(self, |acc, par| {
            let par_span = par.span.clone();
            acc.with_fn_ty_param(par).with_span_opt(Span::hull_opts(par_span, self_span.clone()))
        })
    }

    pub fn matched(
        self,
        cod_pars: impl IntoIterator<Item = (Ident, u128)>,
        cod_body: Self,
        arms: impl IntoIterator<Item = Arm>,
    ) -> Self {
        Self::Match {
            arg: Rc::new(self),
            cod_pars: cod_pars.into_iter().collect(),
            cod_body: Rc::new(cod_body),
            arms: arms.into_iter().collect(),
            span: None,
        }
    }

    pub fn is_type_type(&self) -> bool {
        match self {
            Self::TypeType { .. } => true,
            _ => false,
        }
    }

    pub fn is_atomic(&self) -> bool {
        match self {
            Self::TypeType { .. }
            | Self::Var { .. }
            | Self::Path { .. }
            | Self::Match { .. }
            | Self::Rec { .. }
            | Self::Hole { .. } => true,
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
    #[expect(unused)]
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
    #[allow(dead_code)]
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

    pub fn is_var_with_id(&self, desired_id: u128) -> bool {
        match self {
            Self::Var { id, .. } => *id == desired_id,
            _ => false,
        }
    }

    pub fn is_path_to(&self, desired_path: &Path) -> bool {
        if let Self::Path { path, .. } = self {
            path == desired_path
        } else {
            false
        }
    }

    pub fn is_path_to_ident(&self, ident: &Ident) -> bool {
        if let Self::Path { path: Path { components }, .. } = self
            && let [component] = &components[..]
        {
            component == ident
        } else {
            false
        }
    }

    #[expect(unused)]
    pub fn is_ident_with_name(&self, desired_name: &Ident) -> bool {
        if let Self::Path { path: Path { components }, .. } = self
            && let [name] = &components[..]
        {
            name == desired_name
        } else {
            false
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            Expr::TypeType { span, .. }
            | Expr::Hole { span, .. }
            | Expr::Var { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. } => span.clone(),
        }
    }

    pub fn span_mut(&mut self) -> &mut Option<Span> {
        match self {
            Expr::TypeType { span, .. }
            | Expr::Hole { span, .. }
            | Expr::Var { span, .. }
            | Expr::Path { span, .. }
            | Expr::Fn { span, .. }
            | Expr::FnType { span, .. }
            | Expr::FnApp { span, .. }
            | Expr::Match { span, .. }
            | Expr::Rec { span, .. } => span,
        }
    }

    pub fn displace(&mut self, amount: usize) {
        match self {
            Expr::Var { .. } | Expr::Rec { .. } | Expr::Hole { .. } => (),
            Expr::Path { level, .. } => *level += amount,
            Expr::TypeType { level, .. } => *level += amount,
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.displace(amount);
                Rc::make_mut(body).displace(amount);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.displace(amount);
                Rc::make_mut(cod).displace(amount);
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).displace(amount);
                Rc::make_mut(arg).displace(amount);
            }
            Expr::Match { arg, cod_body, arms, .. } => {
                Rc::make_mut(arg).displace(amount);
                Rc::make_mut(cod_body).displace(amount);
                for arm in arms {
                    arm.body.displace(amount);
                }
            }
        }
    }

    pub fn prefix_paths(&mut self, prefix: &Ident) {
        match self {
            Expr::Rec { .. } | Expr::Hole { .. } | Expr::Var { .. } | Expr::TypeType { .. } => (),
            Expr::Path { path, .. } => *path = path.clone().resolved_in(prefix),
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.prefix_paths(prefix);
                Rc::make_mut(body).prefix_paths(prefix);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.prefix_paths(prefix);
                Rc::make_mut(cod).prefix_paths(prefix);
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).prefix_paths(prefix);
                Rc::make_mut(arg).prefix_paths(prefix);
            }
            Expr::Match { arg, cod_body, arms, .. } => {
                Rc::make_mut(arg).prefix_paths(prefix);
                Rc::make_mut(cod_body).prefix_paths(prefix);
                for arm in arms {
                    arm.body.prefix_paths(prefix);
                }
            }
        }
    }

    pub fn dependencies(&self, this_ind: Option<&Path>) -> Vec<Path> {
        match self {
            Expr::Rec { .. } | Expr::TypeType { .. } | Expr::Hole { .. } | Expr::Var { .. } => {
                Vec::new()
            }
            Expr::Path { path, .. } => {
                if let Some(ind_path) = this_ind
                    && ind_path == path
                {
                    Vec::new()
                } else if path.last_component().name == "elim" {
                    vec![path.clone().parent()]
                } else {
                    vec![path.clone()]
                }
            }
            Expr::Fn { param, body, .. } => param
                .ty
                .dependencies(this_ind)
                .into_iter()
                .chain(body.dependencies(this_ind))
                .collect(),
            Expr::FnType { param, cod, .. } => param
                .ty
                .dependencies(this_ind)
                .into_iter()
                .chain(cod.dependencies(this_ind))
                .collect(),
            Expr::FnApp { func, arg, .. } => {
                func.dependencies(this_ind).into_iter().chain(arg.dependencies(this_ind)).collect()
            }
            Expr::Match { arg, cod_body, arms, .. } => arg
                .dependencies(this_ind)
                .into_iter()
                .chain(cod_body.dependencies(this_ind))
                .chain(arms.iter().map(|arm| arm.body.dependencies(this_ind).into_iter()).flatten())
                .collect(),
        }
    }
}

impl Item {
    pub fn dependencies(&self, path: &Path) -> Vec<Path> {
        match self {
            Item::Def { ty, val } => {
                ty.dependencies(None).into_iter().chain(val.dependencies(None)).collect()
            }
            Item::Axiom { ty } => ty.dependencies(None),
            Item::Inductive { params, ty, constructors } => params
                .iter()
                .map(|p| p.ty.dependencies(None))
                .flatten()
                .chain(ty.dependencies(None))
                .chain(constructors.iter().map(|(_, c)| c.dependencies(Some(&path))).flatten())
                .collect(),
        }
    }

    pub fn prefix_paths(&mut self, prefix: &Ident) {
        match self {
            Item::Def { ty, val } => {
                ty.prefix_paths(prefix);
                val.prefix_paths(prefix);
            }
            Item::Axiom { ty } => ty.prefix_paths(prefix),
            Item::Inductive { params, ty, constructors } => {
                for param in params {
                    param.ty.prefix_paths(prefix);
                }

                ty.prefix_paths(prefix);

                for (_name, ty) in constructors {
                    ty.prefix_paths(prefix);
                }
            }
        }
    }
}

impl Module {
    pub fn new() -> Self {
        Self { submodules: Vec::new(), items: IndexMap::new() }
    }

    pub fn load_from_path_and_name(
        parent_path: &std::path::Path,
        name: &Ident,
        files: &mut SimpleFiles<String, &str>,
    ) -> Result<(std::path::PathBuf, Self)> {
        let mut dir_path = parent_path.to_owned();
        if dir_path.extension().is_some() {
            dir_path.pop();
        }
        dir_path.push(format!("{name}"));
        let file_path = dir_path.with_extension("kwed");
        dir_path.push(format!("Mod.kwed"));

        if dir_path.is_file() {
            match sugared::Module::load_from_file(&dir_path, files) {
                Ok(module) => Ok((dir_path, module.desugared(name)?)),
                Err(e) => {
                    bail!(name.span.clone(), "failed to load module `{name}` from directory: {e}")
                }
            }
        } else if file_path.is_file() {
            match sugared::Module::load_from_file(&file_path, files) {
                Ok(module) => Ok((file_path, module.desugared(name)?)),
                Err(e) => bail!(name.span.clone(), "failed to load module `{name}` from file: {e}"),
            }
        } else {
            bail!(
                name.span.clone(), "failed to locate module `{name}`";
                @note "try creating a file `{name}.kwed` or `{name}/Mod.kwed`"
            )
        }
    }

    pub fn prefix_paths(&mut self, prefix: &Ident) {
        for (_path, item) in &mut self.items {
            item.prefix_paths(prefix);
        }
    }

    pub fn load_submodules(
        &mut self,
        mod_name: &Ident,
        file_path: &std::path::Path,
        files: &mut SimpleFiles<String, &str>,
    ) -> Result<()> {
        let mut new_items = IndexMap::new();

        for submod_name in &self.submodules {
            let (submod_path, mut submod) =
                Self::load_from_path_and_name(file_path, submod_name, files)?;

            submod.bind_vars(); // IMPORTANT:

            submod.load_submodules(submod_name, &submod_path, files)?;

            for (path, item) in submod.items {
                new_items.insert(path.with_prefix(mod_name.clone()), item);
            }
        }

        for (path, item) in mem::take(&mut self.items) {
            new_items.insert(path.with_prefix(mod_name.clone()), item);
        }

        self.items = new_items;

        self.prefix_paths(mod_name);

        Ok(())
    }

    fn get_dependency_path(&self, path: &Path) -> Option<Path> {
        if self.items.contains_key(path) {
            Some(path.clone())
        } else if let Some(Item::Inductive { constructors, .. }) =
            self.items.get(&path.clone().parent())
            && (path.last_component().name == "elim"
                || constructors.iter().any(|(name, _ty)| path.last_component() == name))
        {
            Some(path.clone().parent())
        } else {
            None
        }
    }

    fn topological_sort_visit(
        &self,
        path: Path,
        new_items: &mut IndexMap<Path, Item>,
        visited: &mut Vec<Path>,
    ) -> Result<()> {
        let _guard = log::enter();
        log!("topsort: {path}");

        if new_items.contains_key(&path) {
            return Ok(());
        }

        if let Some(i) = visited.iter().position(|p| p == &path) {
            let cycle: String =
                visited[i..].iter().map(Path::to_string).intersperse(String::from(" → ")).collect();

            bail!(path.span(), "circular definition: `{cycle} → {path}`");
        }

        visited.push(path.clone());

        let item = self.items.get(&path).expect("path should be valid");

        for path in item.dependencies(&path) {
            let Some(dependency_path) = self.get_dependency_path(&path) else {
                bail!(path.span(), "`{}` not found in this scope", path.last_component())
            };

            self.topological_sort_visit(dependency_path, new_items, visited)?;
        }

        new_items.insert(path.clone(), item.clone());

        Ok(())
    }

    pub fn topological_sort(&mut self) -> Result<()> {
        let mut new_items = IndexMap::new();

        for path in self.items.keys() {
            self.topological_sort_visit(path.clone(), &mut new_items, &mut Vec::new())?;
        }

        self.items = new_items;

        Ok(())
    }
}
