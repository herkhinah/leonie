use ::bitvec::vec::BitVec;
use std::{rc::Rc};

use crate::{metas::MetaVar, term::fresh::Fresh, Cxt, Ix, Lvl, Name};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Depth(pub usize);

impl Depth {
    pub fn inc(self) -> Self {
        Self(self.0 + 1)
    }
}

#[derive(Debug, Clone)]
pub enum Term<'src> {
    Tλ(Depth, Name<'src>, Rc<Self>),
    TΠ(Depth, Name<'src>, Rc<Self>, Rc<Self>),
    TLet(Depth, Name<'src>, Rc<Self>, Rc<Self>, Rc<Self>),
    TApp(Depth, Rc<Self>, Rc<Self>),
    TAppPruning(MetaVar, BitVec<usize>),
    TMeta(MetaVar),
    TV(Ix),
    TU,
}

impl<'src> Term<'src> {
    pub fn depth(&self) -> Depth {
        match self {
            Term::Tλ(depth, _, _)
            | Term::TΠ(depth, _, _, _)
            | Term::TLet(depth, _, _, _, _)
            | Term::TApp(depth, _, _) => *depth,
            Term::TAppPruning(_, args) => Depth(args.len()),
            _ => Depth(0),
        }
    }
}

pub struct TPrettyPrinter<'a, 'src>(pub &'a Cxt<'src>, pub &'a Term<'src>);

impl<'a, 'src> std::fmt::Display for TPrettyPrinter<'a, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TPrettyPrinter(cxt, t) = self;

        const ATOM_P: i8 = 3;
        const APP_P: i8 = 2;
        const PI_P: i8 = 1;
        const LET_P: i8 = 0;

        fn parenthize(
            show_parens: impl FnOnce() -> bool,
            f: &mut std::fmt::Formatter<'_>,
            fun: impl FnOnce(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
        ) -> std::fmt::Result {
            if show_parens() {
                write!(f, "(")?;
                fun(f)?;
                write!(f, ")")
            } else {
                fun(f)
            }
        }

        fn show_parens(p_old: i8, p_curr: i8) -> bool {
            p_curr < p_old
        }

        fn print_lambda_body<'src>(
            term: &Term<'src>,
            f: &mut std::fmt::Formatter<'_>,
            fresh: &mut Fresh<'src>,
        ) -> std::fmt::Result {
            match term {
                Term::Tλ(_, x, term) => fresh.with_unfresh(x, |fresh, x| {
                    write!(f, " {x}")?;
                    print_lambda_body(term, f, fresh)
                }),
                other => {
                    write!(f, ". ")?;
                    print(LET_P, other, f, fresh)
                }
            }
        }

        fn print<'src>(
            prec: i8,
            term: &Term<'src>,
            f: &mut std::fmt::Formatter<'_>,
            fresh: &mut Fresh<'src>,
        ) -> std::fmt::Result {
            match &term {
                Term::TV(x) => {
                    write!(f, "{}", fresh[*x])
                }
                Term::Tλ(_, x, ref term) => fresh.with_unfresh(x, |fresh, x| {
                    parenthize(
                        || show_parens(prec, LET_P),
                        f,
                        |f| {
                            write!(f, "λ {x}")?;
                            print_lambda_body(term, f, fresh)
                        },
                    )
                }),
                Term::TΠ(_, x, a, ref b) => parenthize(
                    || show_parens(prec, PI_P),
                    f,
                    |f| {
                        if matches!(x, Name::Elided(_)) {
                            print(APP_P, a, f, fresh)?;
                            write!(f, " → ")?;
                        } else {
                            let x = fresh.freshen(x);
                            write!(f, "({x} : ")?;
                            print(LET_P, a, f, fresh)?;
                            write!(f, ") → ")?;
                        }
                        fresh.with_fresh(x, |fresh, _| print(PI_P, b, f, fresh))
                    },
                ),
                Term::TLet(_, x, a, b, c) => {
                    fresh.with_unfresh(x, |fresh, name| -> std::fmt::Result {
                        write!(f, "let {name} : ")?;

                        print(LET_P, a, f, fresh)?;
                        write!(f, " := ")?;
                        print(LET_P, b, f, fresh)?;

                        writeln!(f, ";")
                    })?;

                    print(LET_P, c, f, fresh)
                }
                Term::TMeta(m) => write!(f, "?{m}"),
                Term::TAppPruning(m, bds) => {
                    let show_parens = || {
                        let mut braces = false;

                        for bound in bds.iter().by_vals() {
                            match bound {
                                true => {
                                    braces = true;
                                    break;
                                }
                                false => {}
                            }
                        }

                        braces && show_parens(prec, APP_P)
                    };

                    parenthize(show_parens, f, |f| {
                        write!(f, "?{m}")?;
                        for (lvl, bound) in bds.iter().by_vals().enumerate() {
                            match bound {
                                true => {
                                    write!(f, " {}", fresh[Lvl(lvl)])?;
                                }
                                false => {}
                            }
                        }

                        Ok(())
                    })
                }
                Term::TApp(_, t, u) => parenthize(
                    || show_parens(prec, APP_P),
                    f,
                    |f| {
                        print(APP_P, t, f, fresh)?;
                        write!(f, " ")?;
                        print(ATOM_P, u, f, fresh)
                    },
                ),
                Term::TU => write!(f, "U"),
            }
        }

        let names: Vec<Name<'src>> = cxt.names.iter().map(|(name, _)| *name).collect();

        print(0, t, f, &mut Fresh::new(names))
    }
}

mod fresh {
    use std::ops::Index;

    use crate::{Ix, Lvl, Name};

    #[derive(Default)]
    pub struct Fresh<'src>(Vec<Name<'src>>, usize);

    impl<'src> Fresh<'src> {
        pub fn new(names: Vec<Name<'src>>) -> Self {
            Self(names, 0)
        }

        pub fn freshen(&mut self, name: &Name<'src>) -> Name<'src> {
            if !self.0.contains(name) {
                *name
            } else {
                self.1 += 1;
                Name::Generated(self.1 - 1)
            }
        }

        pub fn with_fresh<T>(&mut self, name: &Name<'src>, f: impl FnOnce(&mut Self, &Name<'src>) -> T) -> T {
            self.0.push(*name);

            let res = f(self, name);

            self.0.pop();

            res
        }

        pub fn with_unfresh<T>(&mut self, name: &Name<'src>, f: impl FnOnce(&mut Self, &Name<'src>) -> T) -> T {
            let fresh = self.freshen(name);

            self.0.push(fresh);

            let res = f(self, &fresh);

            self.0.pop();

            res
        }
    }

    impl<'src> Index<Ix> for Fresh<'src> {
        type Output = Name<'src>;

        fn index(&self, index: Ix) -> &Self::Output {
            &self.0[self.0.len() - 1 - index.0]
        }
    }

    impl<'src> Index<Lvl> for Fresh<'src> {
        type Output = Name<'src>;

        fn index(&self, index: Lvl) -> &Self::Output {
            &self.0[index.0]
        }
    }
}
