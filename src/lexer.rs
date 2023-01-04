use std::{fmt::Debug, ops::Range};

use bumpalo::Bump;
use chumsky::{
    zero_copy::{
        combinator::Or,
        error::Error,
        prelude::*,
        recursive::{Direct, Indirect},
    },
    BoxStream, Flat, Span,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token<'a> {
    Open(Delim),
    Close(Delim),
    Ident(&'a str),
    Path(Vec<Token<'a>>),
    Ctrl(&'a str),
}

use Token::*;

// Represents the different kinds of delimiters we care about
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Delim {
    Paren(char),
    Block,
}


#[derive(Debug, Clone)]
pub enum TokenTree<'a> {
    Token(Token<'a>),
    Tree(Delim, Vec<(TokenTree<'a>, Range<usize>)>),
}

pub fn lex<'a, 'b, E: Error<str> + Debug + 'a>(input: &'b str) -> (Option<Vec<Token<'a>>>, Vec<E>)
where
    'b: 'a,
{
    let mut tt = Recursive::declare();

    let ctrl = just("->")
        .or(just("→"))
        .or(just("<-"))
        .or(just("←"))
        .or(just("\n"))
        .or(just("\r\n"))
        .or(just(":="))
        .or(just(":"))
        .or(just("="))
        .or(just("\\"))
        .or(just("Π"))
        .or(just("λ"))
        .or(just("_"))
        .or(just("."))
        .map_slice(Token::<'a>::Ctrl);

    let identifier = any()
        .filter(|c: &char| c.is_alphabetic())
        .then(
            any()
                .filter(|c: &char| c.is_alphanumeric() || *c == '_')
                .repeated(),
        )
        .then(any().filter(|c: &char| *c == '\'').repeated())
        .and_is(ctrl.clone().not())
        .map_slice(|s| Token::<'a>::Ident(s));

    let path = identifier
        .clone()
        .separated_by(just('.'))
        .at_least(2)
        .collect::<Vec<_>>()
        .map(|output| Token::<'a>::Path(output));

    let single_token = path
        .or(identifier)
        .or(ctrl)
        .map_with_span(|token, span| (TokenTree::<'a>::Token(token), span));

    let token_tree = tt
        .clone()
        .padded()
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(
            one_of::<[char; 3], str, E, _>(['(', '{', '[']).try_map_with_state(
                |o, _, s: &mut Vec<char>| {
                    s.push(o);
                    Ok(())
                },
            ),
            one_of::<[char; 3], str, E, _>([')', '}', ']']).try_map_with_state(
                |c, span, s: &mut Vec<char>| match (c, s.last()) {
                    (')', Some('(')) => Ok(')'),
                    (']', Some('[')) => Ok(']'),
                    ('}', Some('{')) => Ok('}'),
                    (c, Some('(')) => Err(E::expected_found([Some(')')], Some(c), span)),
                    (c, Some('[')) => Err(E::expected_found([Some(']')], Some(c), span)),
                    (c, Some('{')) => Err(E::expected_found([Some('}')], Some(c), span)),
                    (c, None) => Err(E::expected_found([], Some(c), span)),
                    (_, Some(_)) => panic!(),
                },
            ),
        )
        .map_with_state(|tts, span, state| {
            (
                TokenTree::<'a>::Tree(Delim::Paren(state.pop().unwrap()), tts),
                span,
            )
        });

    tt.define(single_token.clone().or(token_tree.clone()));

    // Whitespace indentation creates code block token trees
    let (res, err) =
        text::semantic_indentation(tt, |tts, span| (TokenTree::Tree(Delim::Block, tts), span))
            .then_ignore(end())
            .parse(input);

    let eoi = 0..input.chars().count();

    (
        res.map(|token_trees| {
            tts_to_stream(eoi, token_trees)
                .fetch_tokens()
                .map(|(token, _)| token)
                .collect::<Vec<_>>()
        }),
        err,
    )
}

/// Flatten a series of token trees into a single token stream, ready for feeding into the main parser
fn tts_to_stream<'a>(
    eoi: Range<usize>,
    token_trees: Vec<(TokenTree<'a>, Range<usize>)>,
) -> BoxStream<'a, Token<'a>, Range<usize>> {
    use std::iter::once;

    BoxStream::from_nested(eoi, token_trees.into_iter(), |(tt, span)| match tt {
        // Single tokens remain unchanged
        TokenTree::Token(token) => Flat::Single((token, span)),
        // Nested token trees get flattened into their inner contents, surrounded by `Open` and `Close` tokens
        TokenTree::Tree(delim, tree) => Flat::Many(
            once((TokenTree::Token(Open(delim)), span.clone()))
                .chain(tree.into_iter())
                .chain(once((TokenTree::Token(Close(delim)), span))),
        ),
    })
}
