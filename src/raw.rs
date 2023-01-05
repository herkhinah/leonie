use std::{alloc::Allocator, ops::Deref};

pub type SourcePos = std::ops::Range<usize>;

#[derive(Debug, Clone, Copy)]
pub enum Raw<'arena> {
    RIdentifier(&'arena str),
    RTypedArgList {
        names: &'arena [Self],
        ty: &'arena Self,
    },
    RLambda {
        args: &'arena [Self],
        expr: &'arena Self,
    },
    RApplication(&'arena Self, &'arena [Self]),
    RU,
    RPi {
        args: &'arena [Self],
        target: &'arena Self,
    },
    RLet {
        name: &'arena Self,
        ty: Option<&'arena Self>,
        definition: &'arena Self,
        scope: &'arena Self,
    },
    RSrcPos((usize, usize), &'arena Self),
    RHole,
}
/*
impl<'a, 'arena, A: Allocator> std::fmt::Display for Raw<'a, 'arena, A> {
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

        fn print<'a, 'arena, A: Allocator>(prec: u8, raw: &Raw<'a, 'arena, A>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match &raw {
                Raw::RSrcPos(_, raw) => print(prec, raw, f),
                Raw::RIdentifier(x) => write!(f, "{x}"),
                Raw::RLambda(x, ref t) => {
                    write!(f, "λ {x}")?;

                    let mut t = t;

                    loop {
                        match &**t {
                            Raw::RLam(x, t_) => {
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
                Raw::RPi(x, a, ref b) => {
                    open(prec, PI_P, f)?;

                    if x.deref() == "_" {
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
                                Raw::RPi(x, a, b_) if x.deref() != "_" => {
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
                Raw::RLet(x, a, b, c) => {
                    write!(f, "let {x} : ")?;

                    print(LET_P, a, f)?;
                    write!(f, " := ")?;
                    print(LET_P, b, f)?;

                    writeln!(f, ";")?;

                    print(LET_P, c, f)
                }
                Raw::RHole => write!(f, "_"),
                Raw::RApp(t, u) => {
                    open(prec, APP_P, f)?;
                    print(APP_P, t, f)?;
                    write!(f, " ")?;
                    print(ATOM_P, u, f)?;
                    close(prec, APP_P, f)
                }
                Raw::RU => write!(f, "U"),
            }
        }

        print(0, self, f)
    }
}
*/
