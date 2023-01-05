use std::ops::Range;

use bumpalo::Bump;
use chumsky::zero_copy::{prelude::*, recursive::Direct};

use crate::lexer::*;
use crate::raw::Raw::{self, *};

use Delim::*;
use Token::*;

pub type TokenInput<'a> = [Token<'a>];

pub type RawLocalScopeParser<'a, 'arena, 'b> =
    Recursive<dyn Parser<'a, TokenInput<'a>, Raw<'arena>, ()> + 'b>;

pub fn raw_local_scope<'a, 'arena, 'b>(
    bump: &'arena Bump,
) -> Recursive<Direct<'b, TokenInput<'a>, Raw<'arena>, ()>>
where
    'arena: 'b,
    'a: 'b + 'arena,
{
    recursive(|raw_local_scope| {
        let mut raw_application = Recursive::declare();
        let mut raw_expr = Recursive::declare();
        let mut raw_type_expr = Recursive::declare();

        parser!(arrow, just(Ctrl("->")).or(just(Ctrl("→"))));

        parser!(
            raw_identifier,
            any().try_map(move |token, span: Range<usize>| match token {
                Ident(ident) => Ok(RSrcPos(
                    (span.start, span.end),
                    bump.alloc(RIdentifier(ident)),
                )),
                found => Err(()),
            })
        );
        parser!(
            raw_universe,
            just::<Token<'a>, TokenInput<'a>, (), ()>(Ident("U")).map(|_| RU)
        );

        parser!(
            raw_named_argument,
            just::<Token<'a>, TokenInput<'a>, (), ()>(Open(Delim::Paren('(')))
                .ignore_then(
                    raw_identifier
                        .clone()
                        .repeated()
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Ctrl(":")))
                .then(raw_type_expr.clone())
                .then_ignore(just(Close(Delim::Paren('('))))
                .map(|(args, ty)| {
                    let args = bump.alloc_slice_copy(&args);
                    RTypedArgList {
                        names: args,
                        ty: bump.alloc(ty),
                    }
                })
        );

        parser!(raw_hole, just(Ctrl("_")).map(|_| RHole));

        parser!(
            atom,
            raw_identifier
                .clone()
                .or(raw_hole.clone())
                .or(raw_universe.clone())
                .or(raw_expr
                    .clone()
                    .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        parser!(
            type_atom,
            raw_identifier
                .clone()
                .or(raw_hole.clone())
                .or(raw_universe)
                .or(raw_type_expr
                    .clone()
                    .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        parser!(unnamed_argument, raw_application.clone().or(atom.clone()));

        parser!(
            raw_lambda,
            just::<Token<'a>, TokenInput<'a>, (), ()>(Ctrl("λ"))
                .or(just(Ctrl("\\")))
                .ignore_then(
                    raw_identifier
                        .clone()
                        .or(raw_named_argument.clone())
                        .repeated()
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Ctrl(".")))
                .then(raw_expr.clone())
                .map(|(identifier, expr)| {
                    let args = bump.alloc_slice_copy(&identifier);
                    RLambda {
                        args,
                        expr: bump.alloc(expr),
                    }
                })
        );

        parser!(
            raw_pi,
            just::<Token<'a>, TokenInput<'a>, (), ()>(Ctrl("Π"))
                .or_not()
                .ignore_then(
                    raw_named_argument
                        .clone()
                        .separated_by(arrow.clone().or_not())
                        .at_least(1)
                        .collect::<Vec<_>>()
                        .or(unnamed_argument.map(|arg| vec![arg])),
                )
                .then_ignore(arrow.clone())
                .then(raw_type_expr.clone())
                .map(|(domain, target)| {
                    let args = bump.alloc_slice_copy(&domain);
                    RPi {
                        args,
                        target: bump.alloc(target),
                    }
                })
        );

        parser!(
            let_binder,
            just::<Token<'a>, TokenInput<'a>, (), ()>(Ident("let"))
                .ignore_then(raw_identifier.clone())
                .then(just(Ctrl(":")).ignore_then(raw_type_expr.clone()).or_not())
                .then(
                    just(Ctrl(":="))
                        .ignore_then(raw_expr.clone())
                        .or(just(Ctrl("\n")).ignore_then(
                            raw_local_scope
                                .clone()
                                .delimited_by(just(Open(Block)), just(Close(Block)))
                        ))
                )
        );

        parser!(
            raw_let,
            let_binder
                .then_ignore(just(Ctrl("\n")).repeated().at_least(1))
                .then(raw_local_scope.clone())
                .map(|(((ident, ty), def), scope)| RLet {
                    name: bump.alloc(ident),
                    ty: ty.map(|ty| &*bump.alloc(ty)),
                    definition: bump.alloc(def),
                    scope: bump.alloc(scope),
                })
        );

        parser!(
            raw_local_scope,
            just(Ctrl("\n")).repeated().ignore_then(
                raw_let
                    .or(raw_expr.clone())
                    .then_ignore(just(Ctrl("\n")).repeated())
            )
        );

        recursive_parser!(
            raw_type_expr,
            raw_pi
                .or(raw_application.clone())
                .or(type_atom.clone())
                .or(raw_type_expr
                    .clone()
                    .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        recursive_parser!(
            raw_application,
            type_atom
                .clone()
                .then(atom.repeated().at_least(1).collect::<Vec<_>>())
                .map(|(rator, rand)| RApplication(bump.alloc(rator), bump.alloc_slice_copy(&rand)))
        );

        recursive_parser!(
            raw_expr,
            raw_lambda.or(raw_type_expr.clone()).or(raw_expr
                .clone()
                .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        raw_local_scope.then_ignore(end())
    })
}

mod parser_macros {
    macro_rules! parser {
        ($name:ident, $def:expr) => {
            #[cfg(feature = "parser_debug")]
            let $name = $crate::parser::debug::ParserDebug::debug($def, stringify!($name));
            #[cfg(not(feature = "parser_debug"))]
            let $name = $def;
        };
    }

    macro_rules! recursive_parser {
        ($name:ident, $def:expr) => {
            #[cfg(feature = "parser_debug")]
            $name.define($crate::parser::debug::ParserDebug::debug(
                $def,
                stringify!($name),
            ));
            #[cfg(not(feature = "parser_debug"))]
            $name.define($def);
        };
    }
    pub(super) use parser;
    pub(super) use recursive_parser;
}

use parser_macros::{parser, recursive_parser};

#[cfg(feature = "parser_debug")]
mod debug {
    use std::marker::PhantomData;
    use std::sync::atomic::AtomicUsize;

    use ansi_term::Color;
    use chumsky::zero_copy::error::Error;
    use chumsky::zero_copy::input::{Input, InputRef};
    use chumsky::zero_copy::internal::{Check, Emit, Mode};
    use chumsky::zero_copy::prelude::*;

    static DEBUG_LEVEL: AtomicUsize = AtomicUsize::new(0usize);

    #[derive(Clone)]
    pub struct DebugParser<'a, P, O, E, S> {
        inner: P,
        debug_msg: &'static str,
        phantom: PhantomData<&'a (O, E, S)>,
    }

    pub trait ParserDebug<'a, P, I: ?Sized, O, E, S> {
        fn debug(self, msg: &'static str) -> DebugParser<'a, P, O, E, S>;
    }

    impl<'a, P, I, O, E, S> ParserDebug<'a, P, I, O, E, S> for P
    where
        P: Parser<'a, I, O, E, S> + Clone,
        I: Input + ?Sized,
        E: Error<I>,
        S: 'a,
    {
        fn debug(self, msg: &'static str) -> DebugParser<'a, P, O, E, S> {
            DebugParser {
                inner: self,
                debug_msg: msg,
                phantom: PhantomData,
            }
        }
    }

    impl<'a, P, I, O, E, S> Parser<'a, I, O, E, S> for DebugParser<'a, P, O, E, S>
    where
        P: Parser<'a, I, O, E, S>,
        I: Input + ?Sized,
        E: Error<I>,
        S: 'a,
    {
        fn go<M: Mode>(
            &self,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<M, O, E>
        where
            Self: Sized,
        {
            let level = DEBUG_LEVEL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

            use ansi_term::Color::{self, *};

            let mut pipes = String::new();
            // TODO: make this more gay, use pride flags as background color and the inverse? color for the lines

            let mut colorwheel = {
                let light_blue = Black.on(RGB(91, 206, 250));
                let pink = Black.on(RGB(245, 169, 184));
                let white = Black.on(White);

                let red = Black.on(RGB(228, 3, 3));
                let orange = Black.on(RGB(255, 140, 0));
                let yellow = Black.on(RGB(255, 237, 0));
                let green = Black.on(RGB(0, 128, 38));
                let indigo = Black.on(RGB(36, 64, 142));
                let violet = Black.on(RGB(115, 41, 130));

                [
                    light_blue, pink, white, pink, light_blue, red, orange, yellow, green, indigo,
                    violet,
                ]
                .into_iter()
                .cycle()
            };

            for _ in 0..level {
                let colored_pipe = format!("{}│ ", colorwheel.next().unwrap().prefix());
                pipes.push_str(colored_pipe.as_str());
            }

            let current = colorwheel.next().unwrap().prefix().to_string();

            println!("{pipes}{current}┌─ entered {}", self.debug_msg);
            let res = self.inner.go::<M>(inp);

            if res.is_ok() {
                println!("{pipes}{current}└─ success {}", self.debug_msg);
            } else {
                println!("{pipes}{current}└─ failed {}", self.debug_msg);
            }

            DEBUG_LEVEL.store(level, std::sync::atomic::Ordering::Relaxed);

            res
        }

        fn go_emit(
            &self,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<Emit, O, E> {
            Parser::<I, O, E, S>::go::<Emit>(self, inp)
        }

        fn go_check(
            &self,
            inp: &mut InputRef<'a, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<Check, O, E> {
            Parser::<I, O, E, S>::go::<Check>(self, inp)
        }
    }
}
