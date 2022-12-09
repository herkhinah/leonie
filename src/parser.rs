use std::{collections::HashSet, ops::Range, rc::Rc};

use chumsky::{prelude::*, BoxStream, Flat};

use crate::Raw;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    Open(Delim),
    Close(Delim),
    Ctrl(&'static str),
    Var(String),
}

type Span = Range<usize>;

// Represents the different kinds of delimiters we care about
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Delim {
    Paren,
    Block,
}

#[derive(Debug)]
enum TokenTree {
    Token(Token),
    Tree(Delim, Vec<(TokenTree, Span)>),
}

#[must_use]
pub fn ident<C: chumsky::text::Character, E: chumsky::Error<C>>(
) -> impl Parser<C, C::Collection, Error = E> + Copy + Clone {
    filter(|c: &C| c.to_char().is_alphabetic())
        .map(Some)
        .chain::<C, Vec<_>, _>(
            filter(|c: &C| c.to_char().is_ascii_alphanumeric() || c.to_char() == '_').repeated(),
        )
        .chain::<C, Vec<_>, _>(filter(|c: &C| c.to_char() == '\'').repeated())
        .collect()
}

fn lexer() -> impl Parser<char, Vec<(TokenTree, Span)>, Error = Simple<char>> {
    let tt = recursive(|tt| {
        // Define some atomic tokens
        let ident = ident().map(Token::Var);
        let ctrl = just("->")
            .or(just("<-"))
            .or(just("=="))
            .or(just(":="))
            .or(just("λ"))
            .or(just("Π"))
            .or(just("."))
            .or(just("\\"))
            .or(just("_"))
            .or(just(":"))
            .or(just("\n"))
            .or(just("="))
            .map(Token::Ctrl);

        let single_token = ctrl.or(ident).map(TokenTree::Token);

        // Tokens surrounded by parentheses get turned into parenthesised token trees
        let token_tree = tt
            .padded()
            .repeated()
            .delimited_by(just('('), just(')'))
            .map(|tts| TokenTree::Tree(Delim::Paren, tts));

        single_token
            .or(token_tree)
            .map_with_span(|tt, span| (tt, span))
    });

    // Whitespace indentation creates code block token trees
    text::semantic_indentation(tt, |tts, span| (TokenTree::Tree(Delim::Block, tts), span))
        .then_ignore(end())
}

/// Flatten a series of token trees into a single token stream, ready for feeding into the main parser
fn tts_to_stream(
    eoi: Span,
    token_trees: Vec<(TokenTree, Span)>,
) -> BoxStream<'static, Token, Span> {
    use std::iter::once;

    BoxStream::from_nested(eoi, token_trees.into_iter(), |(tt, span)| match tt {
        // Single tokens remain unchanged
        TokenTree::Token(token) => Flat::Single((token, span)),
        // Nested token trees get flattened into their inner contents, surrounded by `Open` and `Close` tokens
        TokenTree::Tree(delim, tree) => Flat::Many(
            once((TokenTree::Token(Token::Open(delim)), span.clone()))
                .chain(tree.into_iter())
                .chain(once((TokenTree::Token(Token::Close(delim)), span))),
        ),
    })
}

pub fn parse(input: &str) -> Result<Option<Raw>, Vec<Simple<Token>>> {
    let tts = lexer().parse(input).unwrap();

    // Next, flatten
    let eoi = 0..input.chars().count();
    let token_stream = tts_to_stream(eoi, tts);

    // At this point, we have a token stream that can be fed into the main parser! Because this is just an example,
    // we're instead going to just collect the token stream into a vector and print it.

    //let flattened_trees = token_stream.fetch_tokens().collect::<Vec<_>>();

    let parser = parse_block();
    let (raw, errors) = parser.parse_recovery(token_stream);

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(raw)
}

pub fn parse_block() -> impl Parser<Token, Raw, Error = Simple<Token>> {
    let keywords = HashSet::from(["let", "U"]);

    let ctrl = |ctrl: &'static str| just(Token::Ctrl(ctrl));
    let p_ident = select! { Token::Var(name) if !keywords.contains(name.as_str()) && !name.as_str().starts_with('_') => Into::<Rc<str>>::into(name) };
    let p_var = p_ident.clone().map(Raw::RVar);
    let p_hole = ctrl("_").map(|_| Raw::RHole);
    let p_u = select! { Token::Var(name) if name.as_str() == "U" => Raw::RU };
    let p_binder = p_ident.clone().or(ctrl("_").map(|_| "_".into()));

    let mut p_raw = Recursive::declare();

    let p_atom = p_var
        .or(p_u)
        .or(p_hole)
        .or(p_raw.clone().delimited_by(
            just(Token::Open(Delim::Block)),
            just(Token::Close(Delim::Block)),
        ))
        .or(p_raw.clone().delimited_by(
            just(Token::Open(Delim::Paren)),
            just(Token::Close(Delim::Paren)),
        ));
    let p_spine = p_atom.clone().then(p_atom.repeated()).map(|(head, spine)| {
        spine
            .into_iter()
            .fold(head, |acc, arg| Raw::RApp(acc.into(), arg.into()))
    });

    let p_arrow_r = ctrl("→").or(ctrl("->"));

    let fun_or_spine = p_spine
        .then(p_arrow_r.clone().ignore_then(p_raw.clone()).or_not())
        .map(|(x, y)| match y {
            Some(y) => Raw::RPi("_".into(), x.into(), y.into()),
            None => x,
        });

    let p_lam = ctrl("λ")
        .ignore_then(p_binder.clone().repeated().at_least(1))
        .then_ignore(ctrl("."))
        .then(p_raw.clone())
        .map(|(x, t)| {
            x.into_iter()
                .rev()
                .fold(t, |body, arg| Raw::RLam(arg, body.into()))
        });
    let p_let = just(Token::Var("let".to_string()))
        .ignore_then(p_binder.clone())
        .then_ignore(ctrl(":"))
        .then(p_raw.clone())
        .then_ignore(ctrl(":="))
        .then(p_raw.clone())
        .then_ignore(ctrl("\n"))
        .then(p_raw.clone())
        .map(|(((x, e1), e2), e3)| Raw::RLet(x, e1.into(), e2.into(), e3.into()));
    let p_pi = p_binder
        .then_ignore(ctrl(":"))
        .then(p_raw.clone())
        .delimited_by(
            just(Token::Open(Delim::Paren)),
            just(Token::Close(Delim::Paren)),
        )
        .then_ignore(p_arrow_r)
        .then(p_raw.clone())
        .map(|((x, a), b)| Raw::RPi(x, a.into(), b.into()));

    p_raw.define(
        p_let
            .or(p_lam)
            .or(p_pi)
            .or(fun_or_spine)
            .map_with_span(|raw, span| Raw::RSrcPos(span, raw.into())),
    );

    p_raw
}
