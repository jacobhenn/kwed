use std::rc::Rc;

use chumsky::prelude::*;

use crate::ast::{
    sugared::{Expr, Item, MatchArm, Module, Param},
    Ident, Path,
};

fn comment() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    just("//").then(just('\n').not().repeated()).ignored()
}

fn pad() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    comment().padded().repeated().padded().ignored()
}

impl Ident {
    fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        text::ident()
            .map(|name| Self { name })
            .labelled("identifier")
            .debug("identifier")
    }

    pub fn new(name: &str) -> Ident {
        Self {
            name: name.to_string(),
        }
    }
}

impl Path {
    pub fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        Ident::parse()
            .separated_by(just('.').padded_by(pad()))
            .at_least(1)
            .map(|components| Self { components })
    }
}

impl Param {
    pub fn parse<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Ident::parse()
            .then_ignore(just(':').padded_by(pad()))
            .then(expr)
            .map(|(name, ty)| Self { name, ty })
            .labelled("parameter")
            .debug("parameter")
    }

    pub fn parse_list<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Vec<Self>, Error = Simple<char>> + 'a {
        Self::parse(expr)
            .separated_by(just(',').padded_by(pad()))
            .allow_trailing()
            .labelled("parameter list")
            .debug("parameter list")
    }
}

impl Item {
    // pub fn parse_inductive_def() -> impl Parser<char, (Path, Self), Error = Simple<char>> {
    //     text::keyword("inductive")
    //         .ignore_then(Path::parse().padded_by(pad()))
    //         .then(
    //             Param::parse_list(Expr::parse())
    //                 .padded_by(pad())
    //                 .delimited_by(just('('), just(')'))
    //                 .or_not(),
    //         )
    //         .then_ignore(just(':').padded_by(pad()))
    //         .then(Expr::parse().padded_by(pad()))
    //         .then(
    //             Param::parse_list(Expr::parse())
    //                 .padded_by(pad())
    //                 .delimited_by(just('{'), just('}')),
    //         )
    //         .map(|(((name, args), ty), constructors)| {
    //             (
    //                 name,
    //                 Self::InductiveDef {
    //                     args: args.unwrap_or_else(Vec::new),
    //                     ty,
    //                     constructors,
    //                 },
    //             )
    //         })
    //         .labelled("inductive definition")
    //         .debug("inductive definition")
    // }

    pub fn parse_def() -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("def")
            .ignore_then(Path::parse().padded_by(pad()))
            .then(
                Param::parse_list(Expr::parse())
                    .padded_by(pad())
                    .delimited_by(just('('), just(')'))
                    .or_not(),
            )
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse().padded_by(pad()))
            .then(
                Expr::parse()
                    .padded_by(pad())
                    .delimited_by(just('{'), just('}')),
            )
            .map(|(((name, args), ty), val)| {
                (
                    name,
                    Self::Def {
                        args: args.unwrap_or_else(Vec::new),
                        ty,
                        val,
                    },
                )
            })
            .labelled("definition")
            .debug("definition")
    }

    pub fn parse() -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        // choice((Self::parse_inductive_def(), Self::parse_def()))
        //     .labelled("item")
        //     .debug("item")
        Self::parse_def()
    }
}

impl MatchArm {
    pub fn parse(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        Path::parse()
            .then(Ident::parse().padded_by(pad()).repeated())
            .then_ignore(just("=>").padded_by(pad()))
            .then(expr)
            .map(|((constructor, args), body)| Self {
                constructor,
                args,
                body,
            })
            .labelled("match arm")
            .debug("match arm")
    }
}

impl Expr {
    pub fn parse_type_type() -> impl Parser<char, Self, Error = Simple<char>> {
        text::keyword("Type").to(Self::TypeType).debug("type type")
    }

    pub fn parse_path() -> impl Parser<char, Self, Error = Simple<char>> {
        Path::parse().map(Self::Path).debug("path expression")
    }

    pub fn parse_fn(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        Param::parse(expr.clone())
            .padded_by(pad())
            .delimited_by(just('['), just(']'))
            .padded_by(pad())
            .then(expr)
            .map(|(param, body)| Self::Fn {
                param: Rc::new(param),
                body: Rc::new(body),
            })
            .labelled("function")
            .debug("function")
    }

    pub fn parse_fn_type(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        Param::parse(expr.clone())
            .padded_by(pad())
            .delimited_by(just('('), just(')'))
            .or(Expr::parse_atomic(expr.clone()).map(|ty| Param {
                name: Ident::new(""),
                ty,
            }))
            .then_ignore(just("→").padded_by(pad()))
            .then(expr)
            .map(|(param, cod)| Self::FnType {
                param: Rc::new(param),
                cod: Rc::new(cod),
            })
            .labelled("function type")
            .debug("function type")
    }

    pub fn parse_fn_application(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        Expr::parse_atomic(expr.clone())
            .then(Expr::parse_atomic(expr).padded_by(pad()).repeated())
            .foldl(|func, arg| Self::FnApp {
                func: Rc::new(func),
                arg: Rc::new(arg),
            })
            .labelled("function application")
            .debug("function application")
    }

    pub fn parse_eq(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        Expr::parse_atomic(expr.clone())
            .then_ignore(just('=').padded_by(pad()))
            .then(Expr::parse_atomic(expr))
            .map(|(lhs, rhs)| Expr::Eq {
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
            })
            .labelled("identity type")
            .debug("identity type")
    }

    pub fn parse_refl(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        text::keyword("refl")
            .ignore_then(expr.padded_by(pad()))
            .map(|arg| Expr::Refl(Rc::new(arg)))
            .labelled("reflexivity invocation")
            .debug("reflexivity invocation")
    }

    pub fn parse_match(
        expr: Recursive<char, Expr, Simple<char>>,
    ) -> impl Parser<char, Self, Error = Simple<char>> + '_ {
        text::keyword("match")
            .ignore_then(Expr::parse_atomic(expr.clone()).padded_by(pad()))
            .then_ignore(text::keyword("to").padded_by(pad()))
            .then(expr.clone().padded_by(pad()))
            .then(
                MatchArm::parse(expr)
                    .padded_by(pad())
                    .separated_by(just(',').padded_by(pad()))
                    .allow_trailing()
                    .delimited_by(just('{'), just('}')),
            )
            .map(|((arg, cod), arms)| Self::Match {
                arg: Rc::new(arg),
                cod: Rc::new(cod),
                arms,
            })
            .labelled("match expression")
            .debug("match expression")
    }

    pub fn parse_in_parens<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        expr.padded_by(pad())
            .delimited_by(just('('), just(')'))
            .debug("expr in parens")
    }

    pub fn parse_atomic<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        choice((
            Self::parse_type_type(),
            Self::parse_path(),
            Self::parse_in_parens(expr),
        ))
        .debug("atomic expression")
    }

    pub fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        recursive(|expr| {
            choice((
                Self::parse_match(expr.clone()),
                Self::parse_refl(expr.clone()),
                Self::parse_fn_type(expr.clone()),
                Self::parse_eq(expr.clone()),
                Self::parse_fn_application(expr.clone()),
                Self::parse_fn(expr.clone()),
                Self::parse_atomic(expr),
            ))
        })
        .labelled("expression")
        .debug("expression")
    }
}

impl Module {
    pub fn parse_final() -> impl Parser<char, Self, Error = Simple<char>> {
        Item::parse()
            .padded_by(pad())
            .repeated()
            .then_ignore(end())
            .map(|items| Self {
                items: items.into_iter().collect(),
            })
    }
}
