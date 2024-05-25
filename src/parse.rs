use crate::ast::{
    sugared::{Expr, Item, MatchArm, Module, Param, Params},
    Ident, Path,
};

use std::{assert_matches::assert_matches, rc::Rc};

use chumsky::prelude::*;

use tracing::trace;

fn comment() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    just("//")
        .then(just('\n').not().repeated())
        .ignored()
        .debug("comment")
}

fn pad() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    comment().padded().repeated().padded().ignored()
}

const SPECIAL_CHARS: &[char] = &['.', ',', ':', '\'', '"', '{', '}', '(', ')', '[', ']', '/'];

const RESERVED_IDENTS: &[&str] = &[
    "def",
    "match",
    "to",
    "inductive",
    "struct",
    "Type",
    "refl",
    "let",
    "module",
    "use",
    "=",
    "=>",
    "→",
];

impl Ident {
    fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        filter(|c: &char| !SPECIAL_CHARS.contains(c) && !c.is_whitespace())
            .repeated()
            .at_least(1)
            .collect::<String>()
            .try_map(|name, span| {
                if RESERVED_IDENTS.contains(&name.as_str()) {
                    Err(Simple::custom(
                        span,
                        format!("`{name}` is a reserved keyword"),
                    ))
                } else {
                    Ok(name)
                }
            })
            // text::ident()
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
            .padded_by(pad())
            .repeated()
            .at_least(1)
            .then_ignore(just(':').padded_by(pad()))
            .then(expr)
            .map(|(names, ty)| Self { names, ty })
            .labelled("parameter")
            .debug("parameter")
    }
}

impl Params {
    pub fn parse<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Param::parse(expr)
            .separated_by(just(',').padded_by(pad()))
            .allow_trailing()
            .map(Params)
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
                Params::parse(Expr::parse())
                    .padded_by(pad())
                    .delimited_by(just('('), just(')'))
                    .or_not(),
            )
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse().padded_by(pad()))
            .then(
                Expr::parse()
                    .padded_by(pad())
                    .delimited_by(just('{'), just('}'))
                    .recover_with(nested_delimiters('{', '}', [], |_| Expr::Error)),
            )
            .map(|(((name, args), ty), val)| {
                (
                    name,
                    Self::Def {
                        args: args.unwrap_or_default(),
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
    pub fn parse<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        let refl_path = Path {
            components: vec![Ident::new("refl")],
        };

        Path::parse()
            .or(text::keyword("refl").to(refl_path))
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

    pub fn parse_fn<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Params::parse(expr.clone())
            .padded_by(pad())
            .delimited_by(just('['), just(']'))
            .padded_by(pad())
            .then(expr)
            .map(|(params, body)| Self::Fn {
                params,
                body: Rc::new(body),
            })
            .recover_with(nested_delimiters('[', ']', [], |_| Expr::Error))
            .labelled("function")
            .debug("function")
    }

    pub fn parse_fn_type<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Params::parse(expr.clone())
            .padded_by(pad())
            .delimited_by(just('('), just(')'))
            .or(Expr::parse_atomic(expr.clone()).map(|ty| {
                Params(vec![Param {
                    names: vec![Ident::new("")],
                    ty,
                }])
            }))
            .then_ignore(just("→").padded_by(pad()))
            .then(expr)
            .map(|(params, cod)| Self::FnType {
                params,
                cod: Rc::new(cod),
            })
            .labelled("function type")
            .debug("function type")
    }

    pub fn parse_fn_application<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Expr::parse_atomic(expr.clone())
            .then(Expr::parse_atomic(expr).padded_by(pad()).repeated())
            .foldl(|func, arg| Self::FnApp {
                func: Rc::new(func),
                arg: Rc::new(arg),
            })
            .labelled("function application")
            .debug("function application")
    }

    pub fn parse_eq<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
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

    pub fn parse_refl<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        text::keyword("refl")
            .ignore_then(expr.padded_by(pad()))
            .map(|arg| Expr::Refl(Rc::new(arg)))
            .labelled("reflexivity invocation")
            .debug("reflexivity invocation")
    }

    pub fn parse_match<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        text::keyword("match")
            .ignore_then(Expr::parse_atomic(expr.clone()).padded_by(pad()))
            .then_ignore(text::keyword("to").padded_by(pad()))
            .then(expr.clone().padded_by(pad()))
            .then(
                MatchArm::parse(expr)
                    .padded_by(pad())
                    .separated_by(just(',').padded_by(pad()))
                    .allow_trailing()
                    .delimited_by(just('{'), just('}'))
                    .map(Some)
                    .recover_with(nested_delimiters('{', '}', [], |_| None)),
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

#[test]
fn test_ident_parse() {
    assert_matches!(Ident::parse().then_ignore(end()).parse("x y z"), Err(..));
    assert_matches!(Ident::parse().then_ignore(end()).parse("=>"), Err(..));
    assert_matches!(Ident::parse().then_ignore(end()).parse("z =>"), Err(..));
    assert_matches!(Ident::parse().then_ignore(end()).parse("refl z"), Err(..));
    assert_matches!(
        Ident::parse()
            .then_ignore(end())
            .parse("refl z => refl f z"),
        Err(..)
    );
    assert_matches!(Ident::parse().then_ignore(end()).parse("refl"), Err(..));
    assert_matches!(Ident::parse().then_ignore(end()).parse("jones"), Ok(..));
    assert_matches!(Ident::parse().then_ignore(end()).parse("ℝ=𝝳"), Ok(..));
}

#[test]
fn test_path_parse() {
    assert_matches!(Path::parse().then_ignore(end()).parse("x y z"), Err(..));
    assert_matches!(Path::parse().then_ignore(end()).parse("x/y/z"), Err(..));
    assert_matches!(Path::parse().then_ignore(end()).parse("x.y.z"), Ok(..));
}

#[test]
fn test_param_parse() {
    let param = || Param::parse(Expr::parse()).then_ignore(end());

    assert_matches!(param().parse("x y z"), Err(..));
    assert_matches!(param().parse(": A"), Err(..));
    assert_matches!(param().parse("x:"), Err(..));
    assert_matches!(param().parse("x: A"), Ok(..));
    assert_matches!(param().parse("x:󰐦"), Ok(..));
}

#[test]
fn test_match_arm_parse() {
    let match_arm = || MatchArm::parse(Expr::parse()).then_ignore(end());

    assert_matches!(match_arm().parse("z -> q"), Err(..));
    assert_matches!(match_arm().parse("z => q"), Ok(..));
}
