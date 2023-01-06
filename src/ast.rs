use std::ops::Deref;

use bumpalo::Bump;

use crate::{common::Span, raw::Raw};

#[derive(Debug, Clone, Copy)]
pub enum Name<'src> {
    Generated(usize),
    Elided(Option<Span>),
    Parsed(Span, &'src str),
}

impl<'src> PartialEq for Name<'src> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Generated(l0), Self::Generated(r0)) => l0 == r0,
            (Self::Parsed(_, l1), Self::Parsed(_, r1)) => l1 == r1,
            _ => false,
        }
    }
}

impl<'src> std::fmt::Display for Name<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Generated(num) => write!(f, "'{num}"),
            Name::Elided(_) => write!(f, "_"),
            Name::Parsed(_, name) => write!(f, "{name}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Ast<'src, 'arena> {
    AIdent(&'src str),
    ALambda(Name<'src>, Option<&'arena Self>, &'arena Self),
    AApplication(&'arena Self, &'arena Self),
    AU,
    APi(Name<'src>, &'arena Self, &'arena Self),
    ALet(Name<'src>, Option<&'arena Self>, &'arena Self, &'arena Self),
    ASrcPos(Span, &'arena Self),
    AHole,
}

pub fn lower<'arena, 'src>(
    raw: Raw<'src, '_>,
    bump: &'arena Bump,
) -> Result<Ast<'src, 'arena>, ()> {
    use Ast::*;
    use Raw::*;

    fn lower_binder_name<'src>(
        raw: Raw<'src, '_>,
    ) -> Result<Name<'src>, ()> {
        match raw {
            RSrcPos(span, RIdentifier(name)) => Ok(Name::Parsed(span, name)),
            RSrcPos(span, RHole) => Ok(Name::Elided(Some(span))),
            _ => Err(()),
        }
    }

    fn lower_type<'arena, 'src>(
        raw: Raw<'src, '_>,
        bump: &'arena Bump,
    ) -> Result<Ast<'src, 'arena>, ()> {
        match raw {
            RSrcPos(span, raw) => Ok(ASrcPos(span, bump.alloc(lower_type(*raw, bump)?))),
            RLambda { .. } | RLet { .. } => Err(()),
            other => lower(other, bump),
        }
    }

    fn lower_rator<'arena, 'src>(
        raw: Raw<'src, '_>,
        bump: &'arena Bump,
    ) -> Result<Ast<'src, 'arena>, ()> {
        match raw {
            RSrcPos(span, expr) => Ok(ASrcPos(span, bump.alloc(lower_rator(*expr, bump)?))),
            RPi { .. } | RLet { .. } | RU => Err(()),
            other => lower(other, bump),
        }
    }

    fn lower_expr<'arena, 'src>(
        raw: Raw<'src, '_>,
        bump: &'arena Bump,
    ) -> Result<Ast<'src, 'arena>, ()> {
        match raw {
            RSrcPos(span, expr) => Ok(ASrcPos(span, bump.alloc(lower_expr(*expr, bump)?))),
            RLet { .. } => Err(()),
            other => lower(other, bump),
        }
    }

    match raw {
        RIdentifier(ident) => Ok(AIdent(ident)),
        RTypedArgList { names, ty } => Err(()),
        RLambda { args, expr } => {
            args.iter()
                .rev()
                .try_fold(lower_expr(*expr, bump)?, |expr, arg| match *arg {
                    RSrcPos(span, RTypedArgList { names, ty }) => {
                        let ty = bump.alloc(lower_type(**ty, bump)?);
                        names.iter().rev().try_fold(expr, |acc, arg| {
                            Ok(ALambda(
                                lower_binder_name(*arg)?,
                                Some(ty),
                                bump.alloc(acc),
                            ))
                        })
                    }
                    RSrcPos(span, RIdentifier(ident)) => {
                        Ok(ALambda(Name::Parsed(span, ident), None, bump.alloc(expr)))
                    }
                    RSrcPos(span, RHole) => {
                        Ok(ALambda(Name::Elided(Some(span)), None, bump.alloc(expr)))
                    }
                    _ => Err(()),
                })
        }
        RApplication(rator, rand) => {
            rand.iter()
                .try_fold(lower_rator(*rator, bump)?, |rator, rand| {
                    Ok(AApplication(
                        bump.alloc(rator),
                        bump.alloc(lower_expr(*rand, bump)?),
                    ))
                })
        }
        RU => Ok(AU),
        RPi { args, target } => {
            args.iter()
                .rev()
                .try_fold(lower_type(*target, bump)?, |expr, arg| match *arg {
                    RSrcPos(span, RTypedArgList { names, ty }) => {
                        let ty = bump.alloc(lower_type(**ty, bump)?);
                        names.iter().rev().try_fold(expr, |acc, arg| {
                            Ok(APi(lower_binder_name(*arg)?, ty, bump.alloc(acc)))
                        })
                    }
                    other => Ok(APi(
                        Name::Elided(None),
                        bump.alloc(lower_type(other, bump)?),
                        bump.alloc(expr),
                    )),
                })
        }
        RLet {
            name,
            ty,
            definition,
            scope,
        } => {
            let name = match name {
                RSrcPos(span, RIdentifier(name)) => Ok(Name::Parsed(*span, name)),
                RSrcPos(span, RHole) => Ok(Name::Elided(Some(*span))),
                _ => Err(()),
            }?;

            let ty = match ty {
                Some(ty) => Some(&*bump.alloc(lower_type(*ty, bump)?)),
                None => None,
            };

            Ok(ALet(
                name,
                ty,
                bump.alloc(lower_expr(*definition, bump)?),
                bump.alloc(lower(*scope, bump)?),
            ))
        }
        RSrcPos(span, raw) => Ok(ASrcPos(span, bump.alloc(lower(*raw, bump)?))),
        RHole => Ok(AHole),
    }
}

impl<'src, 'arena> std::fmt::Display for Ast<'src, 'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const ATOM_P: u8 = 3;
        const APP_P: u8 = 2;
        const PI_P: u8 = 1;
        const LET_P: u8 = 0;

        fn show_parens(p_old: u8, p_curr: u8) -> bool {
            p_curr < p_old
        }

        fn open(p_old: u8, p_curr: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if show_parens(p_old, p_curr) {
                write!(f, "(")?;
            }

            Ok(())
        }

        fn close(p_old: u8, p_curr: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if show_parens(p_old, p_curr) {
                write!(f, ")")?;
            }

            Ok(())
        }

        fn print(prec: u8, raw: &Ast, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match &raw {
                Ast::ASrcPos(_, raw) => print(prec, raw, f),
                Ast::AIdent(x) => write!(f, "{x}"),
                Ast::ALambda(x, _, ref t) => {
                    write!(f, "λ {x}")?;

                    let mut t = t;

                    loop {
                        match &**t {
                            Ast::ALambda(x, _, t_) => {
                                write!(f, " {x}")?;
                                t = t_;
                            }
                            other => {
                                write!(f, ". ")?;
                                print(LET_P, other, f)?;

                                break;
                            }
                        }
                    }

                    close(prec, LET_P, f)
                }
                Ast::APi(x, a, ref b) => {
                    open(prec, PI_P, f)?;

                    if matches!(x, Name::Elided(_)) {
                        print(APP_P, a, f)?;
                        write!(f, " → ")?;
                        print(PI_P, b, f)?;
                    } else {
                        write!(f, "({} : ", x.deref())?;
                        print(LET_P, a, f)?;
                        write!(f, ")")?;

                        let mut b = b;

                        loop {
                            match &**b {
                                Ast::APi(x, a, b_) if !matches!(x, Name::Elided(_)) => {
                                    write!(f, "({} : ", x.deref())?;
                                    print(LET_P, a, f)?;
                                    write!(f, ")")?;

                                    b = b_;
                                }
                                other => {
                                    write!(f, " → ")?;
                                    print(PI_P, other, f)?;
                                    break;
                                }
                            }
                        }
                    }

                    close(prec, PI_P, f)
                }
                Ast::ALet(x, a, b, c) => {
                    write!(f, "let {x} ")?;

                    if let Some(a) = a {
                        write!(f, ": ")?;
                        print(LET_P, a, f)?;
                    }
                    write!(f, " := ")?;
                    print(LET_P, b, f)?;

                    writeln!(f, ";")?;

                    print(LET_P, c, f)
                }
                Ast::AHole => write!(f, "_"),
                Ast::AApplication(t, u) => {
                    open(prec, APP_P, f)?;
                    print(APP_P, t, f)?;
                    write!(f, " ")?;
                    print(ATOM_P, u, f)?;
                    close(prec, APP_P, f)
                }
                Ast::AU => write!(f, "U"),
            }
        }

        print(0, self, f)
    }
}
