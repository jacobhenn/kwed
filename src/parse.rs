use std::{collections::HashMap, ops::Range};

use crate::lex::Token;

use logos::Lexer;

use nom::{
    branch::alt,
    combinator::value,
    multi::many1,
    sequence::{delimited, separated_pair, tuple},
    IResult, Parser,
};

pub type Tokens<'source> = Lexer<'source, Token>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Lex {
        span: Range<usize>,
    },
    Parse {
        expected: Vec<(Range<usize>, Token)>,
    },
}

impl<'src> nom::error::ParseError<Tokens<'src>> for Error {
    fn from_error_kind(_input: Tokens, _kind: nom::error::ErrorKind) -> Self {
        Self::Parse { expected: vec![] }
    }

    fn append(_input: Tokens, _kind: nom::error::ErrorKind, other: Self) -> Self {
        other
    }

    fn from_char(_input: Tokens, _: char) -> Self {
        panic!("Error::from_char shouldn't be called")
    }

    fn or(self, other: Self) -> Self {
        match (self, other) {
            (
                Self::Parse { mut expected },
                Self::Parse {
                    expected: other_expected,
                },
            ) => {
                expected.extend(other_expected);
                Self::Parse { expected }
            }
            (Self::Lex { span }, _) | (_, Self::Lex { span }) => Self::Lex { span },
        }
    }
}

fn token(expected_token: Token) -> impl Fn(Tokens) -> IResult<Tokens, (), Error> {
    move |mut tokens: Tokens| match tokens.next() {
        Some(Ok(token)) if token == expected_token => Ok((tokens, ())),
        Some(Err(())) => Err(nom::Err::Failure(Error::Lex {
            span: tokens.span(),
        })),
        _ => Err(nom::Err::Error(Error::Parse {
            expected: vec![(tokens.span(), expected_token)],
        })),
    }
}

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct Ident<'src> {
    slice: &'src str,
}

impl<'src> Ident<'src> {
    pub fn parse(tokens: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        token(Token::Ident)(tokens).map(|(t, _)| {
            let slice = t.slice();
            (t, Self { slice })
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Param<'src> {
    name: Ident<'src>,
    ty: Expr<'src>,
}

impl<'src> Param<'src> {
    pub fn parse(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        separated_pair(Ident::parse, token(Token::Colon), Expr::parse)
            .map(|(name, ty)| Self { name, ty })
            .parse(lexer)
    }
}

#[derive(Debug, PartialEq)]
pub enum Item<'src> {
    InductiveDef {
        args: Vec<Param<'src>>,
        ty: Expr<'src>,
        constructors: Vec<Param<'src>>,
    },
    Def {
        args: Vec<Param<'src>>,
        ty: Expr<'src>,
        val: Expr<'src>,
    },
}

impl<'src> Item<'src> {
    pub fn parse(lexer: Tokens) -> IResult<Tokens, Self, Error> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MatchArm<'src> {
    constructor: Ident<'src>,
    args: Vec<Ident<'src>>,
    body: Expr<'src>,
}

impl<'src> MatchArm<'src> {
    pub fn parse(lexer: Tokens) -> IResult<Tokens, Self, Error> {
        todo!()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'src> {
    TypeType,
    Ident(Ident<'src>),

    Fn {
        param: Box<Param<'src>>,
        body: Box<Self>,
    },
    FnType {
        param: Box<Param<'src>>,
        cod: Box<Self>,
    },
    FnApplication {
        func: Box<Self>,
        arg: Box<Self>,
    },

    Match {
        arg: Box<Self>,
        cod: Box<Self>,
        arms: Vec<MatchArm<'src>>,
    },
}

impl<'src> Expr<'src> {
    pub fn parse_type_type(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        value(Self::TypeType, token(Token::Type)).parse(lexer)
    }

    pub fn parse_ident(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        Ident::parse.map(Self::Ident).parse(lexer)
    }

    pub fn parse_fn(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        tuple((
            token(Token::Fn),
            token(Token::LParen),
            Param::parse,
            token(Token::RParen),
            token(Token::ThickArrow),
            Expr::parse,
        ))
        .map(|(_, _, param, _, _, body)| Self::Fn {
            param: Box::new(param),
            body: Box::new(body),
        })
        .parse(lexer)
    }

    pub fn parse_fn_type(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        tuple((
            token(Token::LParen),
            Param::parse,
            token(Token::RParen),
            token(Token::Arrow),
            Expr::parse,
        ))
        .map(|(_, param, _, _, cod)| Self::FnType {
            param: Box::new(param),
            cod: Box::new(cod),
        })
        .parse(lexer)
    }

    pub fn parse_fn_application(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        tuple((Self::parse_atomic, many1(Self::parse_atomic))).parse(lexer)
    }

    pub fn parse_match(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        tuple(())
    }

    pub fn parse_in_parens(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        delimited(token(Token::LParen), Self::parse, token(Token::RParen)).parse(lexer)
    }

    pub fn parse_atomic(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {
        alt((
            Self::parse_type_type,
            Self::parse_ident,
            Self::parse_match,
            Self::parse_in_parens,
        ))
    }

    pub fn parse(lexer: Tokens<'src>) -> IResult<Tokens, Self, Error> {}
}

#[derive(Debug, PartialEq)]
pub struct Module<'src> {
    items: HashMap<Ident<'src>, Item<'src>>,
}

impl<'src> Module<'src> {}

#[cfg(test)]
mod tests {
    use super::*;

    use logos::Logos;

    #[test]
    fn ident() {
        let tokens = Token::lexer("_meow_");
        assert_eq!(Ident::parse(tokens).unwrap().1, Ident { slice: "_meow_" });
    }

    #[test]
    fn param() {
        let tokens = Token::lexer("a: b");
        assert_eq!(
            Param::parse(tokens).unwrap().1,
            Param {
                name: Ident { slice: "a" },
                ty: Expr::Ident(Ident { slice: "B" })
            },
        );
    }
}
