use std::{
    fmt::Debug,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use metas::{unify, Error, MetaCxt};
use raw::Raw;
use term::{TPrettyPrinter, Term};
use value::{Type, Value};

pub mod metas;
pub mod parser;
pub mod raw;
pub mod term;
pub mod value;

pub type Name = Rc<str>;

pub type SourcePos = std::ops::Range<usize>;

static LEVEL: AtomicUsize = AtomicUsize::new(0);

type Tm = Box<Term>;
type Ty = Box<Term>;

/// De Bruijn index
#[derive(Clone, Copy)]
pub struct Ix(pub usize);

impl std::fmt::Debug for Ix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// De Bruijn level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Lvl(usize);

impl Lvl {
    pub fn as_index(&self, lvl: Self) -> Ix {
        Ix(lvl.0 - self.0 - 1)
    }

    #[must_use]
    pub fn inc(self) -> Self {
        Lvl(self.0 + 1)
    }

    #[must_use]
    pub fn dec(self) -> Self {
        Lvl(self.0 - 1)
    }
}

impl std::ops::Deref for Lvl {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Lvl {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

type VTy = Box<Value>;

type VTm = Box<Value>;

#[derive(Debug, Clone)]
pub struct Closure(Env, Tm);

impl Closure {
    pub fn new(env: Env, term: Tm) -> Self {
        Closure(env, term)
    }

    pub fn eval(self, metas: &mut MetaCxt, v: Value) -> Value {
        let Closure(mut env, t) = self;
        env.push(v);

        env.eval(metas, *t)
    }
}

mod env {
    use std::{ops::Index, slice::Iter};

    use crate::{
        metas::{MetaCxt, MetaEntry},
        value::Spine,
        Closure, Ix, Lvl, Term, Value, BD,
    };

    #[derive(Debug, Clone, Default)]
    pub struct Env(Vec<Value>);

    impl Env {
        pub fn push(&mut self, value: Value) {
            self.0.push(value)
        }

        pub fn pop(&mut self) -> Option<Value> {
            self.0.pop()
        }

        pub fn iter(&self) -> Iter<Value> {
            self.0.iter()
        }

        pub fn eval_under_binder<T>(
            &mut self,
            value: Value,
            f: impl FnOnce(&mut Self) -> T,
        ) -> (T, Value) {
            self.push(value);
            (f(self), self.pop().unwrap())
        }

        pub fn eval(&mut self, metas: &mut MetaCxt, term: Term) -> Value {
            match term {
                Term::TV(x) => self[x].clone(),
                Term::Tλ(x, t) => Value::Vλ(x, Closure::new(self.clone(), t)),
                Term::TΠ(x, a, b) => {
                    let a = self.eval(metas, *a);

                    Value::VΠ(x, a.into(), Closure::new(self.clone(), b))
                }
                Term::TLet(_, _, t, u) => {
                    let value = self.eval(metas, *t);

                    self.eval_under_binder(value, |env| env.eval(metas, *u)).0
                }
                Term::TMeta(m) => match metas[m].clone() {
                    MetaEntry::Solved(v) => v,
                    MetaEntry::Unsolved => Value::new_flex(m),
                },
                Term::TApp(t, u) => {
                    let t = self.eval(metas, *t);
                    let u = self.eval(metas, *u);

                    t.app(metas, u)
                }
                Term::TU => Value::VU,
                Term::TInsertedMeta(m, bds) => {
                    let mut args = Spine::default();

                    match &metas[m] {
                        MetaEntry::Solved(val) => {
                            let mut val = val.clone();
                            for (t, bds) in self.iter().zip(bds.into_iter()) {
                                if let BD::Bound = bds {
                                    val = val.app(metas, t.clone());
                                }
                            }
                            val
                        }
                        MetaEntry::Unsolved => {
                            for (t, bds) in self.iter().cloned().zip(bds.into_iter()) {
                                if let BD::Bound = bds {
                                    args.push(t.clone());
                                }
                            }

                            Value::VFlex(m, args)
                        }
                    }
                }
            }
        }
    }

    impl Index<Ix> for Env {
        type Output = Value;

        fn index(&self, index: Ix) -> &Self::Output {
            &self.0[self.0.len() - 1 - index.0]
        }
    }

    impl Index<Lvl> for Env {
        type Output = Value;

        fn index(&self, index: Lvl) -> &Self::Output {
            &self.0[index.0]
        }
    }
}

use env::Env;

#[derive(Debug, Copy, Clone)]
pub enum BD {
    Bound,
    Defined,
}

#[derive(Debug, Clone, Default)]
pub struct Cxt {
    /// used for evaluation
    env: Env,
    /// used for unification
    lvl: Lvl,
    /// used for raw name lookup, pretty printing
    types: Vec<(Name, Type)>,
    /// used for fresh meta creation
    bds: Vec<BD>,
    /// used for error reporting
    pos: SourcePos,
}

impl Cxt {
    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn lvl(&self) -> Lvl {
        self.lvl
    }

    pub fn types(&self) -> &Vec<(Name, Type)> {
        &self.types
    }

    pub fn bds(&self) -> &Vec<BD> {
        &self.bds
    }

    pub fn pos(&self) -> &SourcePos {
        &self.pos
    }

    pub fn bind<T>(
        &mut self,
        name: Name,
        r#type: Type,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Type)) {
        self.env.push(Value::new_rigid(self.lvl));
        self.lvl = self.lvl.inc();
        self.types.push((name, r#type));
        self.bds.push(BD::Bound);
        let res = f(self);

        let (name, r#type, _) = self.pop();
        self.lvl = self.lvl.dec();

        (res, (name, r#type))
    }

    pub fn define<T>(
        &mut self,
        name: Name,
        val: Value,
        r#type: Type,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Type, Value)) {
        self.env.push(val);
        self.lvl = self.lvl.inc();
        self.types.push((name, r#type));
        self.bds.push(BD::Defined);
        let res = f(self);
        self.lvl = self.lvl.dec();

        (res, self.pop())
    }

    fn pop(&mut self) -> (Name, Value, Value) {
        self.bds.pop();
        let value = self.env.pop().unwrap();
        let (name, r#type) = self.types.pop().unwrap();

        (name, r#type, value)
    }
}

pub fn check(metas: &mut MetaCxt, cxt: &mut Cxt, raw: Raw, ty: Type) -> Result<Term, Error> {
    fn check_(metas: &mut MetaCxt, cxt: &mut Cxt, raw: Raw, ty: Type) -> Result<Term, Error> {
        Ok(match (raw, ty) {
            (Raw::RSrcPos(pos, t), a) => {
                cxt.pos = pos;
                check(metas, cxt, *t, a)?
            }
            (Raw::RLam(x, t), Value::VΠ(_, a, b)) => {
                let b = b.eval(metas, Value::new_rigid(cxt.lvl));
                let body = cxt.bind(x.clone(), *a, |cxt| check(metas, cxt, *t, b)).0?;
                Term::Tλ(x, body.into())
            }
            (Raw::RLet(x, a, t, u), a_) => {
                let a = check(metas, cxt, *a, Value::VU)?;
                let va = cxt.env.eval(metas, a.clone());
                let t = check(metas, cxt, *t, va.clone())?;
                let vt = cxt.env.eval(metas, t.clone());
                let u = cxt
                    .define(x.clone(), vt, va, |cxt| check(metas, cxt, *u, a_))
                    .0?;
                Term::TLet(x, a.into(), t.into(), u.into())
            }
            (Raw::RHole, _) => metas.fresh_meta(cxt),
            (t, expected) => {
                let (t, inferred) = infer(metas, cxt, t)?;

                unify(metas, cxt.lvl, expected, inferred)?;
                t
            }
        })
    }

    match raw {
        Raw::RSrcPos(pos, t) => {
            cxt.pos = pos;
            check(metas, cxt, *t, ty)
        }
        raw => {
            let level = LEVEL.fetch_add(1, Ordering::Relaxed);
            let quotation = ty.clone().quote(metas, cxt.lvl);
            println!(
                "{}check {raw}: {}",
                " ".repeat(level),
                TPrettyPrinter(cxt, &quotation)
            );
            let res = check_(metas, cxt, raw, ty);
            LEVEL.swap(level, Ordering::Relaxed);
            res
        }
    }
}

pub fn close_val(metas: &mut MetaCxt, cxt: &Cxt, val: Value) -> Closure {
    let lvl = cxt.lvl;
    let env = cxt.env.clone();
    let t = val.quote(metas, lvl.inc());
    Closure::new(env, t.into())
}

pub fn infer(metas: &mut MetaCxt, cxt: &mut Cxt, raw: Raw) -> Result<(Term, Type), Error> {
    fn infer_(metas: &mut MetaCxt, cxt: &mut Cxt, raw: Raw) -> Result<(Term, Type), Error> {
        Ok(match raw {
            Raw::RVar(x) => {
                let mut res = Err(());
                for (ix, (x_, r#type)) in cxt.types.iter().rev().enumerate() {
                    if &x == x_ {
                        res = Ok((Term::TV(Ix(ix)), r#type.clone()));
                        break;
                    }
                }
                match res {
                    Ok(res) => res,
                    Err(_) => panic!("unbound variable {x}"),
                }
            }
            Raw::RLam(mut x, t) => {
                let mut a = {
                    let m = metas.fresh_meta(cxt);
                    cxt.env.eval(metas, m)
                };

                let (t, b) = {
                    let (res, (x_, a_)) = cxt.bind(x, a, |cxt| infer(metas, cxt, *t));
                    (x, a) = (x_, a_);
                    res?
                };

                (
                    Term::Tλ(x.clone(), t.into()),
                    Type::VΠ(x, a.into(), close_val(metas, cxt, b)),
                )
            }
            Raw::RApp(t, u) => {
                let (t, tty) = infer(metas, cxt, *t)?;
                let (a, b) = match metas.force(tty) {
                    Value::VΠ(_, a, b) => (*a, b),
                    tty => {
                        let mut a = {
                            let m = metas.fresh_meta(cxt);
                            cxt.env.eval(metas, m)
                        };
                        let (x, b) = {
                            let (m, (x, a_)) = cxt.bind("a".into(), a, |cxt| metas.fresh_meta(cxt));
                            a = a_;
                            (x, Closure::new(cxt.env.clone(), Box::new(m)))
                        };

                        unify(
                            metas,
                            cxt.lvl,
                            Value::VΠ(x, a.clone().into(), b.clone()),
                            tty,
                        )?;
                        (a, b)
                    }
                };
                let u = check(metas, cxt, *u, a)?;

                let ty = {
                    let ty = cxt.env.eval(metas, u.clone());
                    b.eval(metas, ty)
                };

                (Term::TApp(t.into(), u.into()), ty)
            }
            Raw::RU => (Term::TU, Value::VU),
            Raw::RPi(mut x, a, b) => {
                let a = check(metas, cxt, *a, Value::VU)?;
                let b = {
                    let va = cxt.env.eval(metas, a.clone());
                    let (b, (x_, _)) = cxt.bind(x, va, |cxt| check(metas, cxt, *b, Value::VU));
                    x = x_;
                    b?
                };

                (Term::TΠ(x, a.into(), b.into()), Value::VU)
            }
            Raw::RLet(x, a, t, u) => {
                let a = check(metas, cxt, *a, Value::VU)?;

                let va = cxt.env.eval(metas, a.clone());
                let t = check(metas, cxt, *t, va.clone())?;

                let vt = cxt.env.eval(metas, t.clone());
                let (u, b) = cxt
                    .define(x.clone(), vt, va, |cxt| infer(metas, cxt, *u))
                    .0?;

                (Term::TLet(x, a.into(), t.into(), u.into()), b)
            }
            Raw::RSrcPos(pos, t) => {
                cxt.pos = pos;
                infer(metas, cxt, *t)?
            }
            Raw::RHole => {
                let a = {
                    let m = metas.fresh_meta(cxt);
                    cxt.env.eval(metas, m)
                };
                let t = metas.fresh_meta(cxt);
                (t, a)
            }
        })
    }

    match raw {
        Raw::RSrcPos(pos, raw) => {
            cxt.pos = pos;
            infer(metas, cxt, *raw)
        }
        raw => {
            let level = LEVEL.fetch_add(1, Ordering::Relaxed);
            println!("{}infer {}", " ".repeat(level), &raw);
            let res = infer_(metas, cxt, raw);
            LEVEL.swap(level, Ordering::Relaxed);

            if let Ok((term, value)) = &res {
                let quotation = value.clone().quote(metas, cxt.lvl);
                print!("{}|- {}: ", " ".repeat(level), TPrettyPrinter(cxt, term));
                println!("{}", TPrettyPrinter(cxt, &quotation));
            }

            res
        }
    }
}
