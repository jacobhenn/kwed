use crate::ast::{
    sugared::{Expr, Item, MatchArm, Module, Param, Params},
    Ident, Path,
};

use std::rc::Rc;

#[cfg(test)]
use std::assert_matches::assert_matches;

use chumsky::prelude::*;

fn comment() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    just("//")
        .then(just('\n').not().repeated())
        .ignored()
        .debug("comment")
}

fn pad() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    comment().padded().repeated().padded().ignored()
}

const SPECIAL_CHARS: &[char] = &['.', ',', ':', '{', '}', '(', ')', '[', ']'];

const RESERVED_IDENTS: &[&str] = &[
    "def",
    "match",
    "rec",
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
    "//",
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
            .or_not()
            .map(|names| names.unwrap_or(vec![Ident::new("●")]))
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
    pub fn parse_inductive() -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("inductive")
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
                Params::parse(Expr::parse())
                    .padded_by(pad())
                    .delimited_by(just('{'), just('}')),
            )
            .map(|(((name, params), ty), constructors)| {
                (
                    name,
                    Self::Inductive {
                        params: params.unwrap_or_default(),
                        ty,
                        constructors,
                    },
                )
            })
            .labelled("inductive definition")
            .debug("inductive definition")
    }

    pub fn parse_axiom() -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("axiom")
            .ignore_then(Path::parse().padded_by(pad()))
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse().padded_by(pad()))
            .then_ignore(just(';'))
            .map(|(name, ty)| (name, Self::Axiom { ty }))
    }

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
        choice((
            Self::parse_def(),
            Self::parse_axiom(),
            Self::parse_inductive(),
        ))
        .labelled("item")
        .debug("item")
    }
}

impl MatchArm {
    pub fn parse<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Ident::parse()
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
        text::keyword("Type")
            .map_with_span(|_, span| Self::TypeType { span })
            .debug("type type")
    }

    pub fn parse_path() -> impl Parser<char, Self, Error = Simple<char>> {
        Path::parse()
            .map_with_span(|path, span| Self::Path { path, span })
            .debug("path expression")
    }

    pub fn parse_fn<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Params::parse(expr.clone())
            .padded_by(pad())
            .delimited_by(just('['), just(']'))
            .padded_by(pad())
            .then(expr)
            .map_with_span(|(params, body), span| Self::Fn {
                params,
                body: Box::new(body),
                span,
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
                    names: vec![Ident::new("●")],
                    ty,
                }])
            }))
            .then_ignore(just("→").padded_by(pad()))
            .then(expr)
            .map_with_span(|(params, cod), span| Self::FnType {
                params,
                cod: Box::new(cod),
                span,
            })
            .labelled("function type")
            .debug("function type")
    }

    pub fn parse_fn_application<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Expr::parse_atomic(expr.clone())
            .then(Expr::parse_atomic(expr).padded_by(pad()).repeated())
            .map_with_span(|(func, args), span| Self::FnApp {
                func: Box::new(func),
                args,
                span,
            })
            .labelled("function application")
            .debug("function application")
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
            .map_with_span(|((arg, cod), arms), span| Self::Match {
                arg: Box::new(arg),
                cod: Box::new(cod),
                arms,
                span,
            })
            .labelled("match expression")
            .debug("match expression")
    }

    pub fn parse_rec<'a>() -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        text::keyword("rec")
            .ignore_then(Ident::parse().padded_by(pad()))
            .map_with_span(|var, span| Self::Rec { var, span })
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
            Self::parse_rec(),
            Self::parse_path(),
            Self::parse_in_parens(expr),
        ))
        .debug("atomic expression")
    }

    pub fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        recursive(|expr| {
            choice((
                Self::parse_match(expr.clone()),
                Self::parse_fn_type(expr.clone()),
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
