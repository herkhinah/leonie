use std::{
    fmt::{Debug, Display},
    ops::Deref,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use metas::{unify, Error, MetaCxt, MetaVar};

pub mod metas;
pub mod parser;

pub type Name = Rc<str>;

pub type SourcePos = std::ops::Range<usize>;

static LEVEL: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone)]
pub enum Raw {
    RVar(Name),
    RLam(Name, Box<Raw>),
    RApp(Box<Raw>, Box<Raw>),
    RU,
    RPi(Name, Box<Raw>, Box<Raw>),
    RLet(Name, Box<Raw>, Box<Raw>, Box<Raw>),
    RSrcPos(SourcePos, Box<Raw>),
    RHole,
}

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
type Lvl = usize;

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

type VTy = Box<Value>;

type VTm = Box<Value>;

#[derive(Debug, Clone, Default)]
pub struct Spine(Vec<Value>);

impl Spine {
    pub fn quote(mut self, metas: &mut MetaCxt, lvl: Lvl, tm: Term) -> Term {
        if let Some(u) = self.0.pop() {
            Term::TApp(
                self.quote(metas, lvl, tm).into(),
                u.quote(metas, lvl).into(),
            )
        } else {
            tm
        }
    }

    pub fn push(&mut self, value: Value) {
        self.0.push(value)
    }

    pub fn into_iter(self) -> std::vec::IntoIter<Value> {
        self.0.into_iter()
    }
}

impl std::ops::Deref for Spine {
    type Target = Vec<Value>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    /// unsolved meta variabel
    VFlex(MetaVar, Spine),
    /// bound variable applied to zero or more arguments
    VRigid(Lvl, Spine),
    // lambda closure
    Vλ(Name, Closure),
    // pi type
    VΠ(Name, VTy, Closure),
    // sigma type
    VΣ(Name, VTy, Closure),
    // pair
    Vσ(VTm, VTm),
    // universe
    VU,
}

impl Value {
    pub fn quote(self, metas: &mut MetaCxt, lvl: Lvl) -> Term {
        match self {
            Value::VFlex(m, sp) => sp.quote(metas, lvl, Term::TMeta(m)),
            Value::VRigid(x, sp) => sp.quote(metas, lvl, Term::TV(lvl2ix(lvl, x))),
            Value::Vλ(x, clos) => {
                let val = clos.eval(metas, Value::VRigid(lvl, Spine::default()));
                Term::Tλ(x, val.quote(metas, lvl + 1).into())
            }
            Value::VΠ(x, a, clos) => {
                let a = a.quote(metas, lvl);

                let b = clos.eval(metas, Value::VRigid(lvl, Spine::default()));

                let b = b.quote(metas, lvl + 1);

                Term::TΠ(x, a.into(), b.into())
            }
            Value::VΣ(_, _, _) => todo!(),
            Value::Vσ(_, _) => todo!(),
            Value::VU => Term::TU,
        }
    }
}

fn v_app(metas: &mut MetaCxt, v1: Value, v2: Value) -> Value {
    match v1 {
        Value::VFlex(m, mut sp) => {
            sp.push(v2);
            Value::VFlex(m, sp)
        }
        Value::VRigid(x, mut sp) => {
            sp.push(v2);
            Value::VRigid(x, sp)
        }
        Value::Vλ(_, clos) => clos.eval(metas, v2),
        _ => panic!(),
    }
}

pub type Type = Value;

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
        v_app, Closure, Ix, Lvl, Spine, Term, Value, BD,
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
                Term::Tσ(a, b) => {
                    let a = self.eval(metas, *a);
                    let b = self.eval(metas, *b);

                    Value::Vσ(a.into(), b.into())
                }
                Term::TΣ(name, a, b) => {
                    let a = self.eval(metas, *a);
                    Value::VΣ(name, a.into(), Closure::new(self.clone(), b))
                }
                Term::TLet(_, _, t, u) => {
                    let value = self.eval(metas, *t);

                    self.eval_under_binder(value, |env| env.eval(metas, *u)).0
                }
                Term::TMeta(m) => match metas[m].clone() {
                    MetaEntry::Solved(v) => v,
                    MetaEntry::Unsolved => Value::VFlex(m, Spine::default()),
                },
                Term::TApp(t, u) => {
                    let t = self.eval(metas, *t);
                    let u = self.eval(metas, *u);

                    v_app(metas, t, u)
                }
                Term::TU => Value::VU,
                Term::TInsertedMeta(m, bds) => {
                    let mut args = Spine::default();

                    match &metas[m] {
                        MetaEntry::Solved(val) => {
                            let mut val = val.clone();
                            for (t, bds) in self.iter().zip(bds.into_iter()) {
                                if let BD::Bound = bds {
                                    val = v_app(metas, val, t.clone());
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
            &self.0[index]
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
        self.env.push(Value::VRigid(self.lvl, Spine::default()));
        self.lvl += 1;
        self.types.push((name, r#type));
        self.bds.push(BD::Bound);
        let res = f(self);

        let (name, r#type, _) = self.pop();
        self.lvl -= 1;

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
        self.lvl += 1;
        self.types.push((name, r#type));
        self.bds.push(BD::Defined);
        let res = f(self);
        self.lvl -= 1;

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
                let b = b.eval(metas, Value::VRigid(cxt.lvl, Spine::default()));
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
    let t = val.quote(metas, lvl + 1);
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

pub fn lvl2ix(lvl: Lvl, x: Lvl) -> Ix {
    Ix(lvl - x - 1)
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

        fn index(&self, index: usize) -> &Self::Output {
            &self.0[index]
        }
    }
}

use fresh::Fresh;

impl Display for Raw {
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

        fn print(prec: u8, raw: &Raw, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match &raw {
                Raw::RSrcPos(_, raw) => print(prec, raw, f),
                Raw::RVar(x) => write!(f, "{x}"),
                Raw::RLam(x, ref t) => {
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
                    write!(f, "let {} : ", x)?;

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

struct TPrettyPrinter<'a>(&'a Cxt, &'a Term);

impl<'a> Display for TPrettyPrinter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TPrettyPrinter(cxt, t) = self;

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

        fn print(
            prec: u8,
            term: &Term,
            f: &mut std::fmt::Formatter<'_>,
            fresh: &mut Fresh,
        ) -> std::fmt::Result {
            match &term {
                Term::TV(x) => {
                    write!(f, "{}", fresh[*x])
                }
                Term::Tλ(x, ref t) => {
                    let x = fresh.freshen_and_insert(x.clone());
                    open(prec, LET_P, f)?;
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

                                break;
                            }
                        }
                    }

                    close(prec, LET_P, f)
                }
                Term::TΠ(x, a, ref b) => {
                    open(prec, PI_P, f)?;

                    if x.deref() == "_" {
                        print(APP_P, a, f, fresh)?;
                        write!(f, " → ")?;
                        fresh.freshen_and_insert(x.clone());
                        print(PI_P, b, f, fresh)?;
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
                                    print(PI_P, other, f, fresh)?;
                                    break;
                                }
                            }
                        }
                    }

                    close(prec, PI_P, f)
                }
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

                    braces = braces && show_parens(prec, APP_P);
                    if braces {
                        write!(f, "(?{m}")?;
                    } else {
                        write!(f, "?{m} ")?;
                    }
                    for (lvl, bd) in bds.iter().enumerate() {
                        match bd {
                            BD::Bound => {
                                write!(f, " {}", fresh[lvl])?;
                            }
                            BD::Defined => {}
                        }
                    }

                    if braces {
                        write!(f, ")")?;
                    }

                    Ok(())
                }
                Term::TApp(t, u) => {
                    open(prec, APP_P, f)?;
                    print(APP_P, t, f, fresh)?;
                    write!(f, " ")?;
                    print(ATOM_P, u, f, fresh)?;
                    close(prec, APP_P, f)
                }
                Term::TU => write!(f, "U"),
            }
        }

        let names: Vec<Rc<str>> = cxt.types.iter().map(|x| x.0.clone()).collect();

        print(0, t, f, &mut Fresh::new(names))
    }
}
