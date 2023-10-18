use std::fmt::Display;

#[derive(Clone, Debug)]
pub enum Item {
    Definition(Definition),
    InductiveDefinition(InductiveDefinition),
}

#[derive(Clone, Debug)]
pub struct InductiveDefinition {
    pub name: String,
    pub constructors: Vec<ConstructorDefinition>,
}

#[derive(Clone, Debug)]
pub struct ConstructorDefinition {
    pub name: String,
    pub args: Vec<(String, Expr)>,
}

#[derive(Clone, Debug)]
pub struct Definition {
    pub name: String,
    pub ty: Box<Expr>,
    pub value: Box<Expr>,
}

impl Definition {
    pub fn new(name: String, args: Vec<(String, Expr)>, ty: Expr, value: Expr) -> Self {
        let ty = args
            .iter()
            .rfold(ty, |cod, (arg_name, arg_ty)| Expr::FunctionType {
                variable: arg_name.clone(),
                domain: Box::new(arg_ty.clone()),
                codomain: Box::new(cod),
            });

        let value =
            args.into_iter()
                .rfold(value, |ter, (arg_name, arg_ty)| Expr::FunctionAbstraction {
                    variable: arg_name,
                    domain: Box::new(arg_ty),
                    open_term: Box::new(ter),
                });

        Self {
            name,
            ty: Box::new(ty),
            value: Box::new(value),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Branch {
    pub constructor: String,
    pub arguments: Vec<String>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitExpr {
    pub arg: Box<Expr>,
    pub var: String,
    pub result_ty: Box<Expr>,
    pub branches: Vec<Branch>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Universe,

    FunctionType {
        variable: String,
        domain: Box<Expr>,
        codomain: Box<Expr>,
    },
    FunctionAbstraction {
        variable: String,
        domain: Box<Expr>,
        open_term: Box<Expr>,
    },
    FunctionApplication {
        function: Box<Expr>,
        argument: Box<Expr>,
    },

    PathType {
        src: Box<Expr>,
        dst: Box<Expr>,
        ty: Box<Expr>,
    },

    Ident(String),

    Split(SplitExpr),

    RecursiveCall {
        argument: String,
    },
}

impl Expr {
    pub fn function_type(variable: String, domain: Expr, codomain: Expr) -> Self {
        Self::FunctionType {
            variable,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    pub fn function_abstraction(variable: String, domain: Expr, open_term: Expr) -> Self {
        Self::FunctionAbstraction {
            variable,
            domain: Box::new(domain),
            open_term: Box::new(open_term),
        }
    }

    pub fn function_application(function: Expr, args: Vec<Expr>) -> Self {
        args.into_iter()
            .fold(function, |func, arg| Expr::FunctionApplication {
                function: Box::new(func),
                argument: Box::new(arg),
            })
    }

    pub fn path_type(src: Expr, dst: Expr, ty: Expr) -> Self {
        Self::PathType {
            src: Box::new(src),
            dst: Box::new(dst),
            ty: Box::new(ty),
        }
    }

    pub fn ident(arg: String) -> Self {
        Self::Ident(arg)
    }

    pub fn split(arg: Expr, var: String, result_ty: Expr, branches: Vec<Branch>) -> Self {
        Self::Split(SplitExpr {
            arg: Box::new(arg),
            var,
            result_ty: Box::new(result_ty),
            branches,
        })
    }

    pub fn recursive_call(argument: String) -> Self {
        Self::RecursiveCall { argument }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Universe => write!(f, "Type"),
            Expr::FunctionType {
                variable,
                domain,
                codomain,
            } => write!(f, "({variable} : {domain}) -> {codomain}"),
            Expr::FunctionAbstraction {
                variable,
                domain,
                open_term,
            } => write!(f, "fun ({variable} : {domain}) => {open_term}"),
            Expr::FunctionApplication { function, argument } => write!(f, "{function} {argument}"),
            Expr::PathType { src, dst, ty } => write!(f, "{src} = {dst} : {ty}"),
            Expr::Ident(s) => f.write_str(s),
            Expr::Split(SplitExpr {
                arg,
                var,
                result_ty,
                branches,
            }) => {
                write!(f, "split {arg} to {var} => {result_ty} ")?;
                for Branch {
                    constructor,
                    arguments,
                    value,
                } in branches
                {
                    write!(f, "| {constructor}")?;
                    for arg in arguments {
                        write!(f, " {arg}")?;
                    }
                    write!(f, " => {value}")?;
                }
                write!(f, ".")
            }
            Expr::RecursiveCall { argument } => write!(f, "rec{{{argument}}}"),
        }
    }
}

impl Branch {
    pub fn new(constructor: String, arguments: Vec<String>, value: Expr) -> Self {
        Self {
            constructor,
            arguments,
            value,
        }
    }
}
