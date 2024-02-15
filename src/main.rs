use std::fs;

use anyhow::Result;

use codespan_reporting::files::SimpleFiles;

use logos::Logos;

mod err;

mod lex;

mod parse;

fn main() -> Result<()> {
    let path = std::env::args().skip(1).next().unwrap();

    let src = fs::read_to_string(&path).unwrap();

    let mut files: SimpleFiles<&str, &str> = SimpleFiles::new();
    let file_id = files.add(&path, &src);

    let mut lexer = lex::Token::lexer(&src);

    while let Some(token) = lexer.next() {
        match token {
            Ok(token) => (), /*println!("{:?} => {token:?} @ {:?}", lexer.slice(), lexer.span())*/
            Err(()) => err::emit_one("invalid token", file_id, lexer.span(), &files)?,
        }
    }

    Ok(())
}
