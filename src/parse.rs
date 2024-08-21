use crate::ast::{
    sugared::{Expr, Item, Module, Param, Params},
    Directives, Ident, Path, Span,
};

#[cfg(test)]
use std::assert_matches::assert_matches;
use std::collections::HashMap;

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

const SPECIAL_CHARS: &[char] = &['.', ',', ':', ';', '{', '}', '(', ')', '[', ']'];

const RESERVED_IDENTS: &[&str] = &[
    "def",
    "inductive",
    "struct",
    "Type",
    "let",
    "module",
    "use",
    "notation",
    "→",
    "↑",
    "//",
];

impl Ident {
    // TODO: provide some check for `Ident`, `Path`, or `Item` which errors if it has a name that
    // is exactly a number literal
    fn parse(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
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
            .map_with_span(move |name, range| Self {
                name,
                span: Some(Span { file_id, range }),
            })
            .labelled("identifier")
            .debug("identifier")
    }
}

impl Path {
    pub fn parse(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        Ident::parse(file_id)
            .separated_by(just('.').padded_by(pad()))
            .at_least(1)
            .try_map(|components, span| {
                if let [name] = &components[..]
                    && name.name.parse::<i64>().is_ok()
                {
                    Err(Simple::custom(
                        span,
                        format!("a path may not be a single digit string"),
                    ))
                } else {
                    Ok(components)
                }
            })
            .map(|components| Self { components })
    }
}

impl Param {
    pub fn parse<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Ident::parse(file_id)
            .padded_by(pad())
            .repeated()
            .at_least(1)
            .then_ignore(just(':').padded_by(pad()))
            .or_not()
            .map(|names| names.unwrap_or(vec![Ident::blank()]))
            .then(expr)
            .map(|(names, ty)| Self { names, ty })
            .labelled("parameter")
            .debug("parameter")
    }

    pub fn parse_single<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Ident::parse(file_id)
            .padded_by(pad())
            .then_ignore(just(':').padded_by(pad()))
            .or_not()
            .map(|name| name.unwrap_or_else(Ident::blank))
            .then(expr)
            .map(|(name, ty)| Self {
                names: vec![name],
                ty,
            })
            .labelled("parameter")
            .debug("parameter")
    }
}

impl Params {
    pub fn parse<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Param::parse(file_id, expr)
            .separated_by(just(',').padded_by(pad()))
            .allow_trailing()
            .map(Params)
            .labelled("parameter list")
            .debug("parameter list")
    }

    pub fn parse_singles<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Param::parse_single(file_id, expr)
            .separated_by(just(',').padded_by(pad()))
            .allow_trailing()
            .map(Params)
            .labelled("parameter list")
            .debug("parameter list")
    }
}

impl Item {
    pub fn parse_inductive(
        file_id: usize,
    ) -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("inductive")
            .ignore_then(Path::parse(file_id).padded_by(pad()))
            .then(
                Params::parse(file_id, Expr::parse(file_id))
                    .padded_by(pad())
                    .delimited_by(just('('), just(')'))
                    .or_not(),
            )
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse(file_id).padded_by(pad()))
            .then(
                Ident::parse(file_id)
                    .then_ignore(just(':').padded_by(pad()))
                    .then(Expr::parse(file_id).padded_by(pad()))
                    .separated_by(just(',').padded_by(pad()))
                    .allow_trailing()
                    .padded_by(pad())
                    .delimited_by(just('{'), just('}'))
                    .map(Some)
                    .recover_with(nested_delimiters('{', '}', [], |_| None)),
            )
            .map(|(((name, params), ty), constructors)| {
                (
                    name,
                    Self::Inductive {
                        params: params.unwrap_or_else(Params::default),
                        ty,
                        constructors,
                    },
                )
            })
            .labelled("inductive definition")
            .debug("inductive definition")
    }

    pub fn parse_axiom(file_id: usize) -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("axiom")
            .ignore_then(Path::parse(file_id).padded_by(pad()))
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse(file_id).padded_by(pad()))
            .then_ignore(just(';'))
            .map(|(name, ty)| (name, Self::Axiom { ty }))
    }

    pub fn parse_def(file_id: usize) -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        text::keyword("def")
            .ignore_then(Path::parse(file_id).padded_by(pad()))
            .then(
                Params::parse(file_id, Expr::parse(file_id))
                    .padded_by(pad())
                    .delimited_by(just('('), just(')'))
                    .or_not(),
            )
            .then_ignore(just(':').padded_by(pad()))
            .then(Expr::parse(file_id).padded_by(pad()))
            .then(
                Expr::parse(file_id)
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

    pub fn parse(file_id: usize) -> impl Parser<char, (Path, Self), Error = Simple<char>> {
        choice((
            Self::parse_def(file_id),
            Self::parse_axiom(file_id),
            Self::parse_inductive(file_id),
        ))
        .labelled("item")
        .debug("item")
    }
}

impl Expr {
    pub fn parse_type_type(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        text::keyword("Type")
            .ignore_then(
                text::int(10)
                    .padded_by(pad())
                    .try_map(|s: String, span| {
                        s.parse::<usize>()
                            .map_err(|e| Simple::custom(span, format!("{e}")))
                    })
                    .or_not(),
            )
            .map_with_span(move |level, range| Self::TypeType {
                level: level.unwrap_or(0),
                span: Span::new(file_id, range),
            })
            .debug("type type")
    }

    pub fn parse_displace<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        just('↑')
            .then(pad())
            .ignore_then(text::int(10).padded_by(pad()))
            .try_map(|s: String, span| {
                s.parse::<usize>()
                    .map_err(|e| Simple::custom(span, format!("{e}")))
            })
            .then(expr.padded_by(pad()))
            .map_with_span(move |(amount, arg), range| Self::Displace {
                amount,
                arg: Box::new(arg),
                span: Span::new(file_id, range),
            })
    }

    pub fn parse_path(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        Path::parse(file_id)
            .map_with_span(move |path, range| Self::Path {
                path,
                span: Span::new(file_id, range),
            })
            .debug("path expression")
    }

    pub fn parse_fn<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Params::parse(file_id, expr.clone())
            .padded_by(pad())
            .delimited_by(just('['), just(']'))
            .padded_by(pad())
            .then(expr)
            .map_with_span(move |(params, body), range| Self::Fn {
                params,
                body: Box::new(body),
                span: Span::new(file_id, range),
            })
            .recover_with(nested_delimiters('[', ']', [], |_| Expr::Error))
            .labelled("function")
            .debug("function")
    }

    pub fn parse_fn_type<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Params::parse(file_id, expr.clone())
            .padded_by(pad())
            .delimited_by(just('('), just(')'))
            .or(Expr::parse_atomic(file_id, expr.clone()).map(|ty| {
                Params(vec![Param {
                    names: vec![Ident::blank()],
                    ty,
                }])
            }))
            .then_ignore(just("→").padded_by(pad()))
            .then(expr)
            .map_with_span(move |(params, cod), range| Self::FnType {
                params,
                cod: Box::new(cod),
                span: Span::new(file_id, range),
            })
            .labelled("function type")
            .debug("function type")
    }

    pub fn parse_fn_application<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + Clone + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        Expr::parse_atomic(file_id, expr.clone())
            .then(
                Expr::parse_atomic(file_id, expr)
                    .padded_by(pad())
                    .repeated(),
            )
            .map_with_span(move |(func, args), range| Self::FnApp {
                func: Box::new(func),
                args,
                span: Span::new(file_id, range),
            })
            .labelled("function application")
            .debug("function application")
    }

    pub fn parse_number(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        text::int(10)
            .validate(|s: String, span, emit| match s.parse::<i64>() {
                Ok(n) => n,
                Err(e) => {
                    emit(Simple::custom(span, format!("{e}")));
                    i64::MAX
                }
            })
            .map_with_span(move |number, range| Self::Number {
                number,
                span: Span::new(file_id, range),
            })
    }

    pub fn parse_in_parens<'a>(
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        expr.padded_by(pad())
            .delimited_by(just('('), just(')'))
            .debug("expr in parens")
    }

    pub fn parse_atomic<'a>(
        file_id: usize,
        expr: impl Parser<char, Expr, Error = Simple<char>> + 'a,
    ) -> impl Parser<char, Self, Error = Simple<char>> + 'a {
        choice((
            Self::parse_type_type(file_id),
            Self::parse_path(file_id),
            Self::parse_in_parens(expr),
            Self::parse_number(file_id),
        ))
        .debug("atomic expression")
    }

    pub fn parse(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        recursive(|expr| {
            choice((
                Self::parse_displace(file_id, expr.clone()),
                Self::parse_fn_type(file_id, expr.clone()),
                Self::parse_fn_application(file_id, expr.clone()),
                Self::parse_fn(file_id, expr.clone()),
                Self::parse_atomic(file_id, expr),
            ))
        })
        .labelled("expression")
        .debug("expression")
    }
}

impl Directives {
    pub fn parse() -> impl Parser<char, Self, Error = Simple<char>> {
        just("~]")
            .not()
            .repeated()
            .delimited_by(just("[~"), just("~]"))
            .collect()
            .try_map(|s: String, span| {
                ron::from_str(&s).map_err(|e| Simple::custom(span, format!("{e}")))
            })
    }
}

impl Module {
    fn parse_notation(
        file_id: usize,
    ) -> impl Parser<char, HashMap<String, Expr>, Error = Simple<char>> {
        text::keyword("notation")
            .ignore_then(Ident::parse(file_id).padded_by(pad()).map(|i| i.name))
            .then(
                Expr::parse(file_id)
                    .padded_by(pad())
                    .delimited_by(just('{'), just('}')),
            )
            .padded_by(pad())
            .repeated()
            .collect()
    }

    pub fn parse_final(file_id: usize) -> impl Parser<char, Self, Error = Simple<char>> {
        Directives::parse()
            .or_not()
            .then(Self::parse_notation(file_id))
            .then(Item::parse(file_id).padded_by(pad()).repeated())
            .then_ignore(end())
            .map(|((directives, notation), items)| Self {
                directives: directives.unwrap_or_default(),
                notation,
                items: items.into_iter().collect(),
            })
    }
}

#[test]
fn test_ident_parse() {
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("x y z"), Err(..));
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("=>"), Ok(..));
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("z =>"), Err(..));
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("let z"), Err(..));
    assert_matches!(
        Ident::parse(0)
            .then_ignore(end())
            .parse("refl z => refl f z"),
        Err(..)
    );
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("let"), Err(..));
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("jones"), Ok(..));
    assert_matches!(Ident::parse(0).then_ignore(end()).parse("ℝ=𝝳"), Ok(..));
}

#[test]
fn test_path_parse() {
    assert_matches!(Path::parse(0).then_ignore(end()).parse("x y z"), Err(..));
    assert_matches!(Path::parse(0).then_ignore(end()).parse("x;y;z"), Err(..));
    assert_matches!(Path::parse(0).then_ignore(end()).parse("x.y.z"), Ok(..));
}

#[test]
fn test_displace_parse() {
    let expr = || Expr::parse(0);

    assert_matches!(
        Expr::parse_displace(0, expr())
            .then_ignore(end())
            .parse("↑ 1 meow"),
        Ok(..)
    );
}
