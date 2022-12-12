use std::{fmt::Debug, rc::Rc};

use metas::{unify, Error, MetaCxt};
use raw::Raw;
use term::Term;
use value::{Type, Value};

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

    pub fn eval(self, metas: &mut MetaCxt, v: Value) -> Value {
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
}

pub fn check(
    metas: &mut MetaCxt,
    cxt: &mut Cxt,
    raw: Raw,
    expected_type: Type,
) -> Result<Term, Error> {
    Ok(match (raw, expected_type) {
        (Raw::RSrcPos(pos, raw), expected_type) => {
            cxt.pos = pos;
            check(metas, cxt, *raw, expected_type)?
        }
        (Raw::RLam(lambda_var, lambda_body), Value::VΠ(_, domain, codomain)) => {
            let codomain = codomain.eval(metas, Value::new_rigid(cxt.lvl));
            let lambda_body = cxt
                .bind(lambda_var.clone(), *domain, |cxt| {
                    check(metas, cxt, *lambda_body, codomain)
                })
                .0?;
            Term::Tλ(lambda_var, lambda_body.into())
        }
        (Raw::RLet(binder_name, binder_type, binder_def, scope), expected_type) => {
            let binder_type = check(metas, cxt, *binder_type, Value::VU)?;
            let v_binder_type = cxt.env.eval(metas, binder_type.clone());
            let binder_def = check(metas, cxt, *binder_def, v_binder_type.clone())?;
            let v_binder_def = cxt.env.eval(metas, binder_def.clone());
            let scope = cxt
                .define(binder_name.clone(), v_binder_def, v_binder_type, |cxt| {
                    check(metas, cxt, *scope, expected_type)
                })
                .0?;
            Term::TLet(
                binder_name,
                binder_type.into(),
                binder_def.into(),
                scope.into(),
            )
        }
        (Raw::RHole, _) => metas.fresh_meta(cxt),
        (raw, expected_type) => {
            let (t, inferred_type) = infer(metas, cxt, raw)?;

            unify(metas, cxt.lvl, expected_type, inferred_type)?;
            t
        }
    })
}

pub fn close_val(metas: &mut MetaCxt, cxt: &Cxt, value: Value) -> Closure {
    let lvl = cxt.lvl;
    let env = cxt.env.clone();
    let quoted_term = value.quote(metas, lvl.inc());
    Closure::new(env, quoted_term.into())
}

pub fn infer(metas: &mut MetaCxt, cxt: &mut Cxt, raw: Raw) -> Result<(Term, Type), Error> {
    Ok(match raw {
        Raw::RVar(var) => {
            let mut result = Err(());
            for (ix, (var_, r#type)) in cxt.types.iter().rev().enumerate() {
                if &var == var_ {
                    result = Ok((Term::TV(Ix(ix)), r#type.clone()));
                    break;
                }
            }
            match result {
                Ok(res) => res,
                Err(_) => panic!("unbound variable {var}"),
            }
        }
        Raw::RLam(mut var, term) => {
            let mut inferred_domain = {
                let meta_domain = metas.fresh_meta(cxt);
                cxt.env.eval(metas, meta_domain)
            };

            let (term, inferred_codomain) = {
                let (infer_result, (var_, inferred_domain_)) =
                    cxt.bind(var, inferred_domain, |cxt| infer(metas, cxt, *term));
                (var, inferred_domain) = (var_, inferred_domain_);
                infer_result?
            };

            (
                Term::Tλ(var.clone(), term.into()),
                Type::VΠ(
                    var,
                    inferred_domain.into(),
                    close_val(metas, cxt, inferred_codomain),
                ),
            )
        }
        Raw::RApp(rator, rand) => {
            let (rator, inferred_rator) = infer(metas, cxt, *rator)?;
            let (inferred_rator_domain, inferred_rator_codomain) = match metas.force(inferred_rator)
            {
                Value::VΠ(_, rator_domain, rator_codomain) => (*rator_domain, rator_codomain),
                inferred_rator => {
                    let mut meta_domain = {
                        let meta_domain = metas.fresh_meta(cxt);
                        cxt.env.eval(metas, meta_domain)
                    };
                    let (x, meta_codomain) = {
                        let (meta_codomain, (var_domain, meta_domain_)) =
                            cxt.bind("a".into(), meta_domain, |cxt| metas.fresh_meta(cxt));
                        meta_domain = meta_domain_;
                        (
                            var_domain,
                            Closure::new(cxt.env.clone(), Box::new(meta_codomain)),
                        )
                    };

                    unify(
                        metas,
                        cxt.lvl,
                        Value::VΠ(x, meta_domain.clone().into(), meta_codomain.clone()),
                        inferred_rator,
                    )?;
                    (meta_domain, meta_codomain)
                }
            };
            let checked_rand = check(metas, cxt, *rand, inferred_rator_domain)?;

            let inferred_type = {
                let evaluated_rand = cxt.env.eval(metas, checked_rand.clone());
                inferred_rator_codomain.eval(metas, evaluated_rand)
            };

            (Term::TApp(rator.into(), checked_rand.into()), inferred_type)
        }
        Raw::RU => (Term::TU, Value::VU),
        Raw::RPi(mut var_domain, domain, codomain) => {
            let checked_domain = check(metas, cxt, *domain, Value::VU)?;
            let checked_codomain = {
                let evaluated_domain = cxt.env.eval(metas, checked_domain.clone());
                let (check_result, (var_domain_, _)) =
                    cxt.bind(var_domain, evaluated_domain, |cxt| {
                        check(metas, cxt, *codomain, Value::VU)
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
            let binder_type = check(metas, cxt, *binder_type, Value::VU)?;

            let v_binder_type = cxt.env.eval(metas, binder_type.clone());
            let binder_def = check(metas, cxt, *binder_def, v_binder_type.clone())?;

            let v_binder_def = cxt.env.eval(metas, binder_def.clone());
            let (scope, inferred_scope) = cxt
                .define(binder_name.clone(), v_binder_def, v_binder_type, |cxt| {
                    infer(metas, cxt, *scope)
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
            cxt.pos = pos;
            infer(metas, cxt, *t)?
        }
        Raw::RHole => {
            let hole_type = {
                let m = metas.fresh_meta(cxt);
                cxt.env.eval(metas, m)
            };
            let hole = metas.fresh_meta(cxt);
            (hole, hole_type)
        }
    })
}

pub fn normal_form(env: &mut Env, metas: &mut MetaCxt, term: Term) -> Term {
    env.eval(metas, term).quote(metas, env.level())
}
