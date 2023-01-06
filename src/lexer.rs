use std::{fmt::Debug, ops::Range};

use chumsky::{
    zero_copy::{error::Error, input::Input, prelude::*},
    BoxStream, Flat,
    
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Token<'a> {
    Open(Delim),
    Close(Delim),
    Ident(&'a str),
    Ctrl(&'a str),
}

use Token::*;

use crate::common::Span;

// Represents the different kinds of delimiters we care about
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Delim {
    Paren(char),
    Block,
}

#[derive(Debug, Clone)]
pub enum TokenTree<'a> {
    Token(Token<'a>),
    Tree(Delim, Vec<(TokenTree<'a>, Span)>),
}

pub fn lex<'a, 'b, E: Error<str> + Debug + 'a>(input: &'b str) -> (Option<TokenInput<'a>>, Vec<E>)
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
        .map_slice(Ident);

    let single_token = identifier
        .or(ctrl)
        .map_with_span(|token, span: Range<usize>| (TokenTree::<'a>::Token(token), span.into()));

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
                span.into(),
            )
        });

    tt.define(single_token.or(token_tree));

    // Whitespace indentation creates code block token trees
    let (res, err) =
        text::semantic_indentation(tt, |tts, span| (TokenTree::Tree(Delim::Block, tts), span.into()))
            .then_ignore(end())
            .parse(input);

    let eoi = (0..input.chars().count()).into();

    (
        res.map(|token_trees| {
            TokenInput(
                tts_to_stream(eoi, token_trees)
                    .fetch_tokens()
                    .collect::<Vec<_>>(),
            )
        }),
        err,
    )
}

/// Flatten a series of token trees into a single token stream, ready for feeding into the main parser
fn tts_to_stream(
    eoi: Span,
    token_trees: Vec<(TokenTree<'_>, Span)>,
) -> BoxStream<'_, Token<'_>, Span> {
    use std::iter::once;

    BoxStream::from_nested(eoi, token_trees.into_iter(), |(tt, span)| match tt {
        // Single tokens remain unchanged
        TokenTree::Token(token) => Flat::Single((token, span)),
        // Nested token trees get flattened into their inner contents, surrounded by `Open` and `Close` tokens
        TokenTree::Tree(delim, tree) => Flat::Many(
            once((TokenTree::Token(Open(delim)), span))
                .chain(tree.into_iter())
                .chain(once((TokenTree::Token(Close(delim)), span))),
        ),
    })
}

pub struct TokenInput<'a>(Vec<(Token<'a>, Span)>);

impl<'a> Input for TokenInput<'a> {
    type Offset = usize;

    type Token = Token<'a>;

    type Span = Span;

    fn start(&self) -> Self::Offset {
        0
    }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if offset < self.0.len() {
            (offset + 1, Some(self.0[offset].0))
        } else {
            (offset, None)
        }

    }

    fn span(&self, range: Range<Self::Offset>) -> Self::Span {
        let range = Into::<Span>::into(0..self.0.len()).intersect(range);

        match (range.first(), range.last()) {
            (Some(first), Some(last)) => (self.0[first].1.start..self.0[last].1.end).into(),
            _ => Span::empty()
        }

    }
}
