use bumpalo::Bump;
use chumsky::zero_copy::{prelude::*, recursive::Direct};

use crate::common::Span;
use crate::lexer::*;
use crate::raw::Raw::{self, *};

use Delim::*;
use Token::*;

pub type RawLocalScopeParser<'src, 'arena, 'parser> =
    Recursive<dyn Parser<'src, TokenInput<'src>, Raw<'src, 'arena>, ()> + 'parser>;

pub fn raw_local_scope<'src, 'arena, 'parser>(
    bump: &'arena Bump,
) -> Recursive<Direct<'parser, TokenInput<'src>, Raw<'src, 'arena>, ()>>
where
    'arena: 'parser,
    'src: 'parser + 'arena,
{
    recursive(|raw_local_scope| {
        let mut raw_application = Recursive::declare();
        let mut raw_expr = Recursive::declare();
        let mut raw_type_expr = Recursive::declare();

        parser!(arrow, just(Ctrl("->")).or(just(Ctrl("→"))));

        parser!(
            raw_identifier,
            any().try_map(move |token, span: Span| match token {
                Ident(ident) => Ok(RSrcPos(span, bump.alloc(RIdentifier(ident)),)),
                found => Err(()),
            })
        );
        parser!(raw_universe, just(Ident("U")).map(|_| RU));

        parser!(
            raw_named_argument,
            just(Open(Delim::Paren('(')))
                .ignore_then(raw_identifier.repeated().at_least(1).collect::<Vec<_>>(),)
                .then_ignore(just(Ctrl(":")))
                .then(raw_type_expr.clone())
                .then_ignore(just(Close(Delim::Paren('('))))
                .map_with_span(|(args, ty), span: Span| {
                    let args = bump.alloc_slice_copy(&args);
                    RSrcPos(
                        span,
                        bump.alloc(RTypedArgList {
                            names: args,
                            ty: bump.alloc(ty),
                        }),
                    )
                })
        );

        parser!(raw_hole, just(Ctrl("_")).map(|_| RHole));

        parser!(
            atom,
            raw_identifier.or(raw_hole).or(raw_universe).or(raw_expr
                .clone()
                .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        parser!(
            type_atom,
            raw_identifier
                .or(raw_hole)
                .or(raw_universe)
                .or(raw_type_expr
                    .clone()
                    .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        parser!(unnamed_argument, raw_application.clone().or(atom.clone()));

        parser!(
            raw_lambda,
            just(Ctrl("λ"))
                .or(just(Ctrl("\\")))
                .ignore_then(
                    raw_identifier
                        .or(raw_named_argument.clone())
                        .repeated()
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Ctrl(".")))
                .then(raw_expr.clone())
                .map_with_span(|(identifier, expr), span| {
                    let args = bump.alloc_slice_copy(&identifier);
                    RSrcPos(
                        span,
                        bump.alloc(RLambda {
                            args,
                            expr: bump.alloc(expr),
                        }),
                    )
                })
        );

        parser!(
            raw_pi,
            just(Ctrl("Π"))
                .or_not()
                .ignore_then(
                    raw_named_argument
                        .clone()
                        .or(unnamed_argument)
                        .separated_by(arrow.or_not())
                        .at_least(1)
                        .collect::<Vec<_>>()
                )
                .then(arrow.ignore_then(raw_type_expr.clone()).or_not())
                .try_map(|(mut domain, target), span| {
                    let target = match target {
                        Some(target) => target,
                        None => {
                            if domain.len() > 1 {
                                domain.pop().unwrap()
                            } else {
                                return Err(());
                            }
                        }
                    };
                    let args = bump.alloc_slice_copy(&domain);
                    Ok(RSrcPos(
                        span,
                        bump.alloc(RPi {
                            args,
                            target: bump.alloc(target),
                        }),
                    ))
                })
        );

        parser!(
            let_binder,
            just::<Token<'src>, TokenInput<'src>, (), ()>(Ident("let"))
                .ignore_then(raw_identifier)
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
                .map_with_span(|(((ident, ty), def), scope), span| RSrcPos(
                    span,
                    bump.alloc(RLet {
                        name: bump.alloc(ident),
                        ty: ty.map(|ty| &*bump.alloc(ty)),
                        definition: bump.alloc(def),
                        scope: bump.alloc(scope),
                    })
                ))
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
                .map_with_span(|(rator, rand), span| RSrcPos(
                    span,
                    bump.alloc(RApplication(
                        bump.alloc(rator),
                        bump.alloc_slice_copy(&rand)
                    ))
                ))
        );

        recursive_parser!(
            raw_expr,
            raw_lambda.or(raw_type_expr.clone()).or(raw_expr
                .clone()
                .delimited_by(just(Open(Paren('('))), just(Close(Paren('(')))))
        );

        #[cfg(feature = "parser_debug")]
        return debug::debug(
            raw_local_scope
                .then_ignore(just(Ctrl("\n")).repeated())
                .then_ignore(end()),
            "program",
        );
        #[cfg(not(feature = "parser_debug"))]
        return raw_local_scope
            .then_ignore(just(Ctrl("\n")).repeated())
            .then_ignore(end());
    })
}

mod parser_macros {
    macro_rules! parser {
        ($name:ident, $def:expr) => {
            #[cfg(feature = "parser_debug")]
            let $name = $crate::parser::debug::debug($def, stringify!($name));
            #[cfg(not(feature = "parser_debug"))]
            let $name = $def;
        };
    }

    macro_rules! recursive_parser {
        ($name:ident, $def:expr) => {
            #[cfg(feature = "parser_debug")]
            $name.define($crate::parser::debug::debug($def, stringify!($name)));
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

    use chumsky::zero_copy::error::Error;
    use chumsky::zero_copy::input::{Input, InputRef};
    use chumsky::zero_copy::internal::{Check, Emit, Mode};
    use chumsky::zero_copy::prelude::*;

    static DEBUG_LEVEL: AtomicUsize = AtomicUsize::new(0usize);

    #[derive(Clone, Copy)]
    pub struct Debug<'src, P, O, E, S> {
        inner: P,
        debug_msg: &'static str,
        phantom: PhantomData<&'src (O, E, S)>,
    }

    pub fn debug<'src, P, I, O, E, S>(parser: P, msg: &'static str) -> Debug<'src, P, O, E, S>
    where
        P: Parser<'src, I, O, E, S> + Clone,
        I: Input + ?Sized,
        E: Error<I>,
        S: 'src,
    {
        Debug {
            inner: parser,
            debug_msg: msg,
            phantom: PhantomData,
        }
    }

    impl<'src, P, I, O, E, S> Parser<'src, I, O, E, S> for Debug<'src, P, O, E, S>
    where
        P: Parser<'src, I, O, E, S>,
        I: Input + ?Sized,
        E: Error<I>,
        S: 'src,
    {
        fn go<M: Mode>(
            &self,
            inp: &mut InputRef<'src, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<M, O, E>
        where
            Self: Sized,
        {
            let level = DEBUG_LEVEL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

            use ansi_term::Color::*;

            let mut pipes = String::new();
            let mut colorwheel = [Cyan, White, Green, Purple, Red].into_iter().cycle();

            for _ in 0..level {
                let colored_pipe = format!("{}│ ", colorwheel.next().unwrap().prefix());
                pipes.push_str(colored_pipe.as_str());
            }

            let white = White.prefix().to_string();
            let red = Red.prefix().to_string();
            let green = Green.prefix().to_string();
            let current = colorwheel.next().unwrap().prefix().to_string();

            println!("{pipes}{current}┌─ {white}entered {}", self.debug_msg);
            let res = self.inner.go::<M>(inp);

            if res.is_ok() {
                println!("{pipes}{current}└─ {green}success {}", self.debug_msg);
            } else {
                println!("{pipes}{current}└─ {red}failed {}", self.debug_msg);
            }

            DEBUG_LEVEL.store(level, std::sync::atomic::Ordering::Relaxed);

            res
        }

        fn go_emit(
            &self,
            inp: &mut InputRef<'src, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<Emit, O, E> {
            Parser::<I, O, E, S>::go::<Emit>(self, inp)
        }

        fn go_check(
            &self,
            inp: &mut InputRef<'src, '_, I, E, S>,
        ) -> chumsky::zero_copy::PResult<Check, O, E> {
            Parser::<I, O, E, S>::go::<Check>(self, inp)
        }
    }
}
