use std::{ops::Deref, rc::Rc};

use crate::{metas::MetaVar, term::fresh::Fresh, Cxt, Ix, Lvl, Name, Tm, Ty, BD};

#[derive(Debug, Clone)]
pub enum Term {
    TV(Ix),
    Tλ(Name, Tm),
    TΠ(Name, Ty, Ty),
    TLet(Name, Ty, Tm, Tm),
    TMeta(MetaVar),
    TInsertedMeta(MetaVar, Vec<BD>),
    TApp(Tm, Tm),
    TU,
}

pub struct TPrettyPrinter<'a>(pub &'a Cxt, pub &'a Term);

impl<'a> std::fmt::Display for TPrettyPrinter<'a> {
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

        fn print_lambda_body(
            term: &Term,
            f: &mut std::fmt::Formatter<'_>,
            fresh: &mut Fresh,
        ) -> std::fmt::Result {
            match term {
                Term::Tλ(x, term) => fresh.with_unfresh(x, |fresh, x| {
                    write!(f, " {x}")?;
                    print_lambda_body(term, f, fresh)
                }),
                other => {
                    write!(f, ". ")?;
                    print(LET_P, other, f, fresh)
                }
            }
        }

        fn print(
            prec: i8,
            term: &Term,
            f: &mut std::fmt::Formatter<'_>,
            fresh: &mut Fresh,
        ) -> std::fmt::Result {
            match &term {
                Term::TV(x) => {
                    write!(f, "{}", fresh[*x])
                }
                Term::Tλ(x, ref term) => fresh.with_unfresh(x, |fresh, x| {
                    parenthize(
                        || show_parens(prec, LET_P),
                        f,
                        |f| {
                            write!(f, "λ {x}")?;
                            print_lambda_body(term, f, fresh)
                        },
                    )
                }),
                Term::TΠ(x, a, ref b) => parenthize(
                    || show_parens(prec, PI_P),
                    f,
                    |f| {
                        if x.deref() == "_" {
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
                Term::TLet(x, a, b, c) => {
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
                Term::TInsertedMeta(m, bds) => {
                    let show_parens = || {
                        let mut braces = false;

                        for bd in bds {
                            match bd {
                                BD::Bound => {
                                    braces = true;
                                    break;
                                }
                                BD::Defined => {}
                            }
                        }

                        braces && show_parens(prec, APP_P)
                    };

                    parenthize(show_parens, f, |f| {
                        write!(f, "?{m}")?;
                        for (lvl, bd) in bds.iter().enumerate() {
                            match bd {
                                BD::Bound => {
                                    write!(f, " {}", fresh[Lvl(lvl)])?;
                                }
                                BD::Defined => {}
                            }
                        }

                        Ok(())
                    })
                }
                Term::TApp(t, u) => parenthize(
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

        let names: Vec<Rc<str>> = cxt.types.iter().map(|x| x.0.clone()).collect();

        print(0, t, f, &mut Fresh::new(names))
    }
}

mod fresh {
    use std::ops::{Deref, Index};

    use crate::{Ix, Lvl, Name};

    #[derive(Default)]
    pub struct Fresh(Vec<Name>);

    impl Fresh {
        pub fn new(names: Vec<Name>) -> Self {
            Self(names)
        }

        pub fn freshen(&self, name: &Name) -> Name {
            if !self.0.contains(name) {
                name.clone()
            } else {
                self.freshen(&format!("{}'", name.deref()).into_boxed_str().into())
            }
        }

        pub fn with_fresh<T>(&mut self, name: &Name, f: impl FnOnce(&mut Self, &Name) -> T) -> T {
            self.0.push(name.clone());

            let res = f(self, name);

            self.0.pop();

            res
        }

        pub fn with_unfresh<T>(&mut self, name: &Name, f: impl FnOnce(&mut Self, &Name) -> T) -> T {
            let fresh = self.freshen(name);

            self.0.push(fresh.clone());

            let res = f(self, &fresh);

            self.0.pop();

            res
        }
    }

    impl Index<Ix> for Fresh {
        type Output = Name;

        fn index(&self, index: Ix) -> &Self::Output {
            &self.0[self.0.len() - 1 - index.0]
        }
    }

    impl Index<Lvl> for Fresh {
        type Output = Name;

        fn index(&self, index: Lvl) -> &Self::Output {
            &self.0[index.0]
        }
    }
}
