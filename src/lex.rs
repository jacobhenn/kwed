#[derive(Debug, PartialEq, Eq, Clone, Copy, logos::Logos)]
#[logos(skip r"[ \t\n\f]")]
pub enum Token {
    // delimiters
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,

    #[token("{")]
    LCurly,
    #[token("}")]
    RCurly,

    // punctuation
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("=")]
    Eq,
    #[token("->")]
    Arrow,
    #[token("*")]
    Star,
    #[token("=>")]
    ThickArrow,

    // keywords
    #[token("Type")]
    Type,
    #[token("inductive")]
    Inductive,
    #[token("def")]
    Def,
    #[token("match")]
    Match,
    #[token("rec")]
    Rec,
    #[token("fn")]
    Fn,

    // identifiers
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Ident,
}
