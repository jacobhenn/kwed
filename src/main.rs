mod ast;

mod eval;

use crate::{ast::Item, eval::Context};

use anyhow::{bail, Context as _};

use lalrpop_util::lalrpop_mod;

use tracing_subscriber::filter::EnvFilter;

lalrpop_mod!(pub ast_parser);

fn remove_comments(s: &str) -> String {
    let mut chars = s.chars().peekable();
    let mut res = String::new();

    let mut in_comment = false;
    loop {
        match (chars.next(), chars.peek()) {
            (Some('('), Some('~')) => in_comment = true,
            (Some('~'), Some(')')) => {
                in_comment = false;
                chars.next();
            }
            (Some(c), _) => {
                if in_comment {
                    res.push(' ');
                } else {
                    res.push(c)
                }
            }
            _ => break,
        }
    }

    res
}

#[test]
fn test_remove_comments() {
    assert_eq!(remove_comments("meow (~ meow ~)"), "meow ");
    assert_eq!(remove_comments("(~ meow ~) meow"), " meow");
    assert_eq!(remove_comments("meow (~ meow ~) meow"), "meow  meow");
    assert_eq!(remove_comments("(~ meow ~)"), "");
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::Subscriber::builder()
        .pretty()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let path = std::env::args().skip(1).next().unwrap();
    let src = std::fs::read_to_string(path).context("failed to open file")?;
    let src = remove_comments(&src);

    let module = match ast_parser::ModuleParser::new().parse(&src) {
        Ok(m) => m,
        Err(e) => bail!("parse error: {:#}", e),
    };

    // println!("parsed module: {module:#?}");

    let mut context = Context::prelude();

    for item in module {
        // println!("parsed item: {item:#?}");

        match item {
            Item::Definition(d) => context.add_definition(d)?,
            Item::InductiveDefinition(d) => context.add_inductive_definition(d)?,
        }
    }

    println!("type checking successful");

    Ok(())
}
