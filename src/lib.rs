use std::{fmt::Debug, rc::Rc};

use error::{Error, ErrorKind};
use metas::{unify, MetaCxt};
use raw::Raw;
use term::Term;
use value::{Type, Value};

#[macro_use]
pub mod error;
pub mod metas;
pub mod parser;
pub mod raw;
pub mod term;
pub mod value;

#[cfg(test)]
mod tests;

pub type Name = Rc<str>;

pub type SourcePos = std::ops::Range<usize>;

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

#[derive(Debug, Clone)]
pub struct Closure(Env, Tm);

impl Closure {
    pub fn new(env: Env, term: Tm) -> Self {
        Closure(env, term)
    }

    pub fn eval(self, v: Value, metas: &mut MetaCxt) -> Value {
        let Closure(mut env, t) = self;
        env.push(v);

        env.eval(metas, *t)
    }
}

pub mod env {
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
                Term::TV(ix) => self[ix].clone(),
                Term::Tλ(var, body) => Value::Vλ(var, Closure::new(self.clone(), body)),
                Term::TΠ(var, domain, codomain) => {
                    let domain = self.eval(metas, *domain);

                    Value::VΠ(var, domain.into(), Closure::new(self.clone(), codomain))
                }
                Term::TLet(_, _, bound_term, scope) => {
                    let value = self.eval(metas, *bound_term);

                    self.eval_under_binder(value, |env| env.eval(metas, *scope))
                        .0
                }
                Term::TMeta(m) => match metas[m].clone() {
                    MetaEntry::Solved(v) => v,
                    MetaEntry::Unsolved => Value::new_flex(m),
                },
                Term::TApp(rator, rand) => {
                    let rator = self.eval(metas, *rator);
                    let rand = self.eval(metas, *rand);

                    rator.app(metas, rand)
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

        pub fn level(&self) -> Lvl {
            Lvl(self.0.len())
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

    pub metas: MetaCxt,
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
        var_name: Name,
        var_type: Type,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Type)) {
        self.env.push(Value::new_rigid(self.lvl));
        self.lvl = self.lvl.inc();
        self.types.push((var_name, var_type));
        self.bds.push(BD::Bound);
        let res = scope(self);

        let (name, var_type, _) = self.pop();
        self.lvl = self.lvl.dec();

        (res, (name, var_type))
    }

    pub fn define<T>(
        &mut self,
        binder_name: Name,
        binder_def: Value,
        binder_type: Type,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Type, Value)) {
        self.env.push(binder_def);
        self.lvl = self.lvl.inc();
        self.types.push((binder_name, binder_type));
        self.bds.push(BD::Defined);
        let res = scope(self);
        self.lvl = self.lvl.dec();

        (res, self.pop())
    }

    fn pop(&mut self) -> (Name, Value, Value) {
        self.bds.pop();
        let value = self.env.pop().unwrap();
        let (var_name, var_type) = self.types.pop().unwrap();

        (var_name, var_type, value)
    }

    pub fn check(&mut self, raw: Raw, expected_type: Type) -> Result<Term, Error> {
        Ok(match (raw, expected_type) {
            (Raw::RSrcPos(pos, raw), expected_type) => {
                self.pos = pos;
                self.check(*raw, expected_type)?
            }
            (Raw::RLam(lambda_var, lambda_body), Value::VΠ(_, domain, codomain)) => {
                let codomain = codomain.eval(Value::new_rigid(self.lvl), &mut self.metas);
                let lambda_body = self
                    .bind(lambda_var.clone(), *domain, |cxt| {
                        cxt.check(*lambda_body, codomain)
                    })
                    .0?;
                Term::Tλ(lambda_var, lambda_body.into())
            }
            (Raw::RLet(binder_name, binder_type, binder_def, scope), expected_type) => {
                let binder_type = self.check(*binder_type, Value::VU)?;
                let v_binder_type = self.env.eval(&mut self.metas, binder_type.clone());
                let binder_def = self.check(*binder_def, v_binder_type.clone())?;
                let v_binder_def = self.env.eval(&mut self.metas, binder_def.clone());
                let scope = self
                    .define(binder_name.clone(), v_binder_def, v_binder_type, |cxt| {
                        cxt.check(*scope, expected_type)
                    })
                    .0?;
                Term::TLet(
                    binder_name,
                    binder_type.into(),
                    binder_def.into(),
                    scope.into(),
                )
            }
            (Raw::RHole, _) => self.fresh_meta(),
            (raw, expected_type) => {
                let (t, inferred_type) = self.infer(raw)?;

                unify(&mut self.metas, self.lvl, expected_type, inferred_type)?;
                t
            }
        })
    }

    pub fn close_val(&mut self, value: Value) -> Closure {
        let lvl = self.lvl;
        let env = self.env.clone();
        let quoted_term = value.quote(&mut self.metas, lvl.inc());
        Closure::new(env, quoted_term.into())
    }

    pub fn infer(&mut self, raw: Raw) -> Result<(Term, Type), Error> {
        Ok(match raw {
            Raw::RVar(var) => {
                let mut result = Err(());
                for (ix, (var_, r#type)) in self.types.iter().rev().enumerate() {
                    if &var == var_ {
                        result = Ok((Term::TV(Ix(ix)), r#type.clone()));
                        break;
                    }
                }

                result.map_err(|_| error!(ErrorKind::Unbound))?
            }
            Raw::RLam(mut var, term) => {
                let mut inferred_domain = {
                    let meta_domain = self.fresh_meta();
                    self.eval(meta_domain)
                };

                let (term, inferred_codomain) = {
                    let (infer_result, (var_, inferred_domain_)) =
                        self.bind(var, inferred_domain, |cxt| cxt.infer(*term));
                    (var, inferred_domain) = (var_, inferred_domain_);
                    infer_result?
                };

                (
                    Term::Tλ(var.clone(), term.into()),
                    Type::VΠ(
                        var,
                        inferred_domain.into(),
                        self.close_val(inferred_codomain),
                    ),
                )
            }
            Raw::RApp(rator, rand) => {
                let (rator, inferred_rator) = self.infer(*rator)?;
                let (inferred_rator_domain, inferred_rator_codomain) = match self
                    .metas
                    .force(inferred_rator)
                {
                    Value::VΠ(_, rator_domain, rator_codomain) => (*rator_domain, rator_codomain),
                    inferred_rator => {
                        let mut meta_domain = {
                            let meta_domain = self.fresh_meta();
                            self.eval(meta_domain)
                        };
                        let (x, meta_codomain) = {
                            let (meta_codomain, (var_domain, meta_domain_)) =
                                self.bind("a".into(), meta_domain, |cxt| cxt.fresh_meta());
                            meta_domain = meta_domain_;
                            (
                                var_domain,
                                Closure::new(self.env.clone(), Box::new(meta_codomain)),
                            )
                        };

                        let lvl = self.lvl;
                        unify(
                            &mut self.metas,
                            lvl,
                            Value::VΠ(x, meta_domain.clone().into(), meta_codomain.clone()),
                            inferred_rator,
                        )?;
                        (meta_domain, meta_codomain)
                    }
                };
                let checked_rand = self.check(*rand, inferred_rator_domain)?;

                let inferred_type = {
                    let evaluated_rand = self.eval(checked_rand.clone());
                    inferred_rator_codomain.eval(evaluated_rand, &mut self.metas)
                };

                (Term::TApp(rator.into(), checked_rand.into()), inferred_type)
            }
            Raw::RU => (Term::TU, Value::VU),
            Raw::RPi(mut var_domain, domain, codomain) => {
                let checked_domain = self.check(*domain, Value::VU)?;
                let checked_codomain = {
                    let evaluated_domain = self.eval(checked_domain.clone());
                    let (check_result, (var_domain_, _)) =
                        self.bind(var_domain, evaluated_domain, |cxt| {
                            cxt.check(*codomain, Value::VU)
                        });
                    var_domain = var_domain_;
                    check_result?
                };

                (
                    Term::TΠ(var_domain, checked_domain.into(), checked_codomain.into()),
                    Value::VU,
                )
            }
            Raw::RLet(binder_name, binder_type, binder_def, scope) => {
                let binder_type = self.check(*binder_type, Value::VU)?;

                let v_binder_type = self.eval(binder_type.clone());
                let binder_def = self.check(*binder_def, v_binder_type.clone())?;

                let v_binder_def = self.eval(binder_def.clone());
                let (scope, inferred_scope) = self
                    .define(binder_name.clone(), v_binder_def, v_binder_type, |cxt| {
                        cxt.infer(*scope)
                    })
                    .0?;

                (
                    Term::TLet(
                        binder_name,
                        binder_type.into(),
                        binder_def.into(),
                        scope.into(),
                    ),
                    inferred_scope,
                )
            }
            Raw::RSrcPos(pos, t) => {
                self.pos = pos;
                self.infer(*t)?
            }
            Raw::RHole => {
                let hole_type = {
                    let m = self.fresh_meta();
                    self.eval(m)
                };
                let hole = self.fresh_meta();
                (hole, hole_type)
            }
        })
    }

    pub fn normal_form(&mut self, term: Term) -> Term {
        self.eval(term).quote(&mut self.metas, self.env.level())
    }

    fn eval(&mut self, term: Term) -> Value {
        let Self { env, metas, .. } = self;

        env.eval(metas, term)
    }

    fn fresh_meta(&mut self) -> Term {
        let Self { bds, metas, .. } = self;

        metas.fresh_meta(bds)
    }
}
