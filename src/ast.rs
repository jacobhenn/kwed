use crate::eval::{
    Branch, Expr, FunctionAbstraction, FunctionApplication, FunctionType, InductiveDefinition,
    PathType, SplitExpr,
};

use std::{collections::HashMap, fmt::Display};

#[derive(Clone, Debug)]
pub enum Item {
    Definition(Definition),
    InductiveDefinition(InductiveDefinition),
}

#[derive(Clone, Debug)]
pub struct Definition {
    pub name: String,
    pub ty: Box<Expr>,
    pub value: Box<Expr>,
}

impl Definition {
    pub fn new(name: String, args: Vec<(String, Expr)>, ty: Expr, value: Expr) -> Self {
        let ty = args.iter().rfold(ty, |cod, (arg_name, arg_ty)| {
            Expr::function_type(arg_name.clone(), arg_ty.clone(), cod)
        });

        let value = args.into_iter().rfold(value, |ter, (arg_name, arg_ty)| {
            Expr::function_abstraction(arg_name, arg_ty, ter)
        });

        Self {
            name,
            ty: Box::new(ty),
            value: Box::new(value),
        }
    }
}

impl Expr {
    pub fn function_type(variable: String, domain: Expr, codomain: Expr) -> Self {
        Self::FunctionType(FunctionType {
            var: variable,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        })
    }

    pub fn function_abstraction(variable: String, domain: Expr, open_term: Expr) -> Self {
        Self::FunctionAbstraction(FunctionAbstraction {
            var: variable,
            domain: Box::new(domain),
            open_term: Box::new(open_term),
        })
    }

    pub fn function_application(function: Expr, args: Vec<Expr>) -> Self {
        args.into_iter().fold(function, |func, arg| {
            Expr::FunctionApplication(FunctionApplication {
                function: Box::new(func),
                argument: Box::new(arg),
            })
        })
    }

    pub fn path_type(src: Expr, dst: Expr, ty: Expr) -> Self {
        Self::PathType(PathType {
            src: Box::new(src),
            dst: Box::new(dst),
            ty: Box::new(ty),
        })
    }

    pub fn ident(arg: String) -> Self {
        Self::Ident(arg)
    }

    pub fn split(arg: Expr, var: String, result_ty: Expr, branches: Vec<(String, Branch)>) -> Self {
        Self::Split(SplitExpr {
            arg: Box::new(arg),
            var,
            result_ty: Box::new(result_ty),
            branches: branches.into_iter().collect(),
        })
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Universe => write!(f, "Type"),
            Expr::FunctionType(FunctionType {
                var,
                domain,
                codomain,
            }) => {
                if var.is_empty() {
                    write!(f, "{domain} -> {codomain}")
                } else {
                    write!(f, "({var} : {domain}) -> {codomain}")
                }
            }
            Expr::FunctionAbstraction(FunctionAbstraction {
                var: variable,
                domain,
                open_term,
            }) => write!(f, "fun ({variable} : {domain}) => {open_term}"),
            Expr::FunctionApplication(FunctionApplication { function, argument }) => {
                write!(f, "{function} {argument}")
            }
            Expr::PathType(PathType { src, dst, ty }) => write!(f, "{src} = {dst} : {ty}"),
            Expr::Ident(s) => f.write_str(s),
            Expr::Split(SplitExpr {
                arg,
                var,
                result_ty,
                branches,
            }) => {
                write!(f, "split {arg} to {var} => {result_ty}")?;
                for (constructor, Branch { arguments, value }) in branches {
                    write!(f, " | {constructor}")?;
                    for arg in arguments {
                        write!(f, " {arg}")?;
                    }
                    write!(f, " => {value}")?;
                }
                write!(f, ".")
            }
            Expr::RecursiveCall(argument) => write!(f, "rec{{{argument}}}"),
        }
    }
}
