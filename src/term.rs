use std::{ops::Deref, rc::Rc};

use crate::{metas::MetaVar, term::fresh::Fresh, Cxt, Ix, Lvl, Name, Tm, Ty, BD};

#[derive(Debug, Clone)]
pub enum Term {
    TV(Ix),
    Tλ(Name, Tm),
    TΠ(Name, Ty, Ty),
    Tσ(Tm, Tm),
    TΣ(Name, Ty, Ty),
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
                Term::Tλ(x, ref t) => parenthize(
                    || show_parens(prec, LET_P),
                    f,
                    |f| {
                        let x = fresh.freshen_and_insert(x.clone());

                        write!(f, "λ {x}")?;
                        let mut t = t;
                        loop {
                            match &**t {
                                Term::Tλ(x, t_) => {
                                    let x = fresh.freshen_and_insert(x.clone());
                                    write!(f, " {x}")?;
                                    t = t_;
                                }
                                other => {
                                    write!(f, ". ")?;
                                    print(LET_P, other, f, fresh)?;

                                    break Ok(());
                                }
                            }
                        }
                    },
                ),
                Term::TΠ(x, a, ref b) => parenthize(
                    || show_parens(prec, PI_P),
                    f,
                    |f| {
                        if x.deref() == "_" {
                            print(APP_P, a, f, fresh)?;
                            write!(f, " → ")?;
                            fresh.freshen_and_insert(x.clone());
                            print(PI_P, b, f, fresh)
                        } else {
                            fresh.freshen_and_insert_after(
                                x.clone(),
                                |fresh, x| -> std::fmt::Result {
                                    write!(f, "({x} : ")?;
                                    print(LET_P, a, f, fresh)?;
                                    write!(f, ")")
                                },
                            )?;

                            let mut b = b;

                            loop {
                                match &**b {
                                    Term::TΠ(x, a, b_) if x.deref() != "_" => {
                                        fresh.freshen_and_insert_after(
                                            x.clone(),
                                            |fresh, x| -> std::fmt::Result {
                                                write!(f, "({x} : ")?;
                                                print(LET_P, a, f, fresh)?;
                                                write!(f, ")")
                                            },
                                        )?;

                                        b = b_;
                                    }
                                    other => {
                                        write!(f, " → ")?;
                                        break print(PI_P, other, f, fresh);
                                    }
                                }
                            }
                        }
                    },
                ),
                Term::Tσ(_, _) => todo!(),
                Term::TΣ(_, _, _) => todo!(),
                Term::TLet(x, a, b, c) => {
                    fresh.freshen_and_insert_after(
                        x.clone(),
                        |fresh, name| -> std::fmt::Result {
                            write!(f, "let {} : ", name)?;

                            print(LET_P, a, f, fresh)?;
                            write!(f, " := ")?;
                            print(LET_P, b, f, fresh)?;

                            writeln!(f, ";")?;

                            Ok(())
                        },
                    )?;

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

        pub fn freshen_and_insert(&mut self, name: Name) -> Name {
            let name = self.freshen(name);
            self.0.push(name.clone());
            name
        }

        fn freshen(&self, name: Name) -> Name {
            if name.deref() == "_" || !self.0.contains(&name) {
                name
            } else {
                self.freshen(format!("{}'", name.deref()).into_boxed_str().into())
            }
        }

        pub fn eval<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
            let old_len = self.0.len();

            let res = f(self);

            while old_len > self.0.len() {
                self.0.pop();
            }

            res
        }

        pub fn freshen_and_insert_after<T>(
            &mut self,
            name: Name,
            f: impl FnOnce(&mut Self, &Name) -> T,
        ) -> T {
            let name = self.freshen(name);

            let res = self.eval(|this| f(this, &name));

            self.0.push(name);

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
