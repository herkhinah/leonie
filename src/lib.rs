#![feature(arc_unwrap_or_clone, allocator_api)]

pub mod lexer;
pub mod parser;
pub mod raw;

/*
use ::bitvec::vec::BitVec;
use error::{Error, ErrorKind};
use metas::MetaCxt;
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

pub type Name = Rc<str>;

pub type SourcePos = std::ops::Range<usize>;

type Tm = Rc<Term>;
type Ty = Rc<Term>;

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

pub type VTy = Rc<Value>;

#[derive(Debug, Clone)]
pub struct Closure(Env, Rc<Term>);

impl Closure {
    pub fn from(env: &Env, term: Rc<Term>) -> Self {
        let depth = term.depth().0 + 1;
        Self(env.clone_with_capacity(depth), term)
    }

    pub fn eval(self, v: Rc<Value>, metas: &mut MetaCxt) -> Rc<Value> {
        let Closure(mut env, t) = self;
        env.push(v);

        env.eval(metas, Rc::<Term>::unwrap_or_clone(t))
    }
}

pub mod env {
    use crate::{
        metas::{MetaCxt, MetaEntry},
        value::Spine,
        Closure, Ix, Lvl, Term, Value,
    };
    use std::{ops::Index, rc::Rc, slice::Iter};

    #[derive(Debug, Clone, Default)]
    pub struct Env(Vec<Rc<Value>>);

    impl Env {
        pub fn with_capacity(len: usize) -> Self {
            Self(Vec::with_capacity(len))
        }

        pub fn clone_with_capacity(&self, len: usize) -> Self {
            let mut vec = Vec::with_capacity(self.0.len() + len);
            self.0.clone_into(&mut vec);
            Self(vec)
        }

        pub fn push(&mut self, value: Rc<Value>) {
            self.0.push(value)
        }

        pub fn pop(&mut self) -> Option<Rc<Value>> {
            self.0.pop()
        }

        pub fn iter(&self) -> Iter<Rc<Value>> {
            self.0.iter()
        }

        #[inline(always)]
        pub fn eval_under_binder<T>(
            &mut self,
            value: Rc<Value>,
            f: impl FnOnce(&mut Self) -> T,
        ) -> (T, Rc<Value>) {
            self.push(value);
            (f(self), self.pop().unwrap())
        }

        pub fn reserve_and_eval(&mut self, metas: &mut MetaCxt, term: Term) -> Rc<Value> {
            self.0.reserve(term.depth().0);

            self.eval(metas, term)
        }

        pub fn eval(&mut self, metas: &mut MetaCxt, term: Term) -> Rc<Value> {
            match term {
                Term::TV(ix) => self[ix].clone(),
                Term::Tλ(_, var, body) => Value::Vλ(var, Closure::from(self, body)).into(),
                Term::TΠ(_, var, domain, codomain) => {
                    let domain = self.eval(metas, Rc::unwrap_or_clone(domain));

                    Value::VΠ(var, domain, Closure::from(self, codomain)).into()
                }
                Term::TLet(_, _, _, bound_term, scope) => {
                    let value = self.eval(metas, Rc::unwrap_or_clone(bound_term));

                    self.eval_under_binder(value, |env| env.eval(metas, Rc::unwrap_or_clone(scope)))
                        .0
                }
                Term::TMeta(m) => match metas[m].clone() {
                    MetaEntry::Solved(v, _) => v.into(),
                    MetaEntry::Unsolved(_) => Value::new_flex(m).into(),
                },
                Term::TApp(_, rator, rand) => {
                    let rand = self.eval(metas, Rc::unwrap_or_clone(rand));
                    let rator = self.eval(metas, Rc::unwrap_or_clone(rator));

                    Rc::unwrap_or_clone(rator).app(metas, rand)
                }
                Term::TU => Value::VU.into(),
                Term::TAppPruning(m, bds) => {
                    let mut args = Spine::default();

                    match &metas[m] {
                        MetaEntry::Solved(val, _) => {
                            let mut val = val.clone();
                            for (idx, t) in self.iter().enumerate() {
                                if bds[idx] {
                                    val = Rc::unwrap_or_clone(val.app(metas, t.clone()));
                                }
                            }
                            val.into()
                        }
                        MetaEntry::Unsolved(_) => {
                            for (idx, t) in self.iter().cloned().enumerate() {
                                if bds[idx] {
                                    args.push(t.clone());
                                }
                            }

                            Value::VFlex(m, args).into()
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
        type Output = Rc<Value>;

        fn index(&self, index: Ix) -> &Self::Output {
            &self.0[self.0.len() - 1 - index.0]
        }
    }

    impl Index<Lvl> for Env {
        type Output = Rc<Value>;

        fn index(&self, index: Lvl) -> &Self::Output {
            &self.0[index.0]
        }
    }
}

use env::Env;

#[derive(Debug, Clone)]
pub enum Local {
    Bound(Name, Rc<Term>),
    Defined(Name, Rc<Term>, Rc<Term>),
}

#[derive(Debug, Clone, Default)]
pub struct Cxt {
    /// used for evaluation
    env: Env,
    /// used for unification
    lvl: Lvl,
    /// mask of bound variables
    pruning: BitVec<usize>,
    /// getting types of fresh metas
    locals: Vec<Local>,
    /// names used for lookup during elaboration
    names: Vec<(Name, Rc<Type>)>,
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

    pub fn bds(&self) -> &Vec<Local> {
        &self.locals
    }

    pub fn pos(&self) -> &SourcePos {
        &self.pos
    }

    #[inline(always)]
    pub fn bind<T>(
        &mut self,
        var_name: Name,
        v_var_type: Rc<Type>,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Rc<Type>)) {
        self.env.push(Value::new_rigid(self.lvl).into());
        let var_type = (*v_var_type).clone().quote(&mut self.metas, self.lvl);

        self.lvl = self.lvl.inc();
        self.locals
            .push(Local::Bound(var_name.clone(), var_type.into()));
        self.pruning.push(true);
        self.names.push((var_name, v_var_type));
        let res = scope(self);

        self.lvl = self.lvl.dec();
        self.env.pop();
        self.pruning.pop();
        self.locals.pop();
        (res, self.names.pop().unwrap())
    }

    #[inline(always)]
    pub fn define<T>(
        &mut self,
        binder_name: Name,
        binder_def: Rc<Term>,
        v_binder_def: Rc<Value>,
        binder_type: Rc<Term>,
        v_binder_type: Rc<Value>,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name, Rc<Term>, Rc<Type>, Rc<Term>, Rc<Value>)) {
        self.env.push(v_binder_def);
        self.lvl = self.lvl.inc();

        self.names.push((binder_name.clone(), v_binder_type));
        self.locals
            .push(Local::Defined(binder_name, binder_type, binder_def));
        self.pruning.push(false);

        let res = scope(self);

        self.lvl = self.lvl.dec();
        self.pruning.pop();
        let (binder_type, binder_def) = match self.locals.pop().unwrap() {
            Local::Defined(_, binder_type, binder_def) => (binder_type, binder_def),
            _ => panic!(),
        };

        let (name, v_binder_type) = self.names.pop().unwrap();
        (
            res,
            (
                name,
                binder_type,
                v_binder_type,
                binder_def,
                self.env.pop().unwrap(),
            ),
        )
    }

    pub fn check(&mut self, raw: Raw, mut expected_type: Rc<Type>) -> Result<Term, Error> {
        match raw {
            Raw::RSrcPos(pos, raw) => {
                self.pos = pos;
                Ok(self.check(*raw, expected_type)?)
            }

            Raw::RLet(binder_name, binder_type, binder_def, scope) => {
                let binder_type: Rc<Term> = self.check(*binder_type, Value::VU.into())?.into();
                let v_binder_type = self.eval((*binder_type).clone());
                let binder_def: Rc<Term> = self.check(*binder_def, v_binder_type.clone())?.into();
                let v_binder_def = self.eval((*binder_def).clone());
                let (scope, (binder_name, binder_type, _, binder_def, _)) = self.define(
                    binder_name,
                    binder_def,
                    v_binder_def,
                    binder_type,
                    v_binder_type,
                    |cxt| cxt.check(*scope, expected_type),
                );

                let scope = scope?;

                let depth = std::cmp::max(
                    std::cmp::max(binder_def.depth(), scope.depth().inc()),
                    binder_type.depth(),
                );

                Ok(Term::TLet(
                    depth,
                    binder_name,
                    binder_type,
                    binder_def,
                    scope.into(),
                ))
            }
            Raw::RHole => Ok(self.fresh_meta(expected_type)),

            mut raw => {
                if matches!(&raw, Raw::RLam(_, _)) {
                    (raw, expected_type) =
                        match (raw, self.metas.force(Rc::unwrap_or_clone(expected_type))) {
                            (
                                Raw::RLam(lambda_var, lambda_body),
                                Value::VΠ(_, domain, codomain),
                            ) => {
                                let codomain = codomain
                                    .eval(Value::new_rigid(self.lvl).into(), &mut self.metas);
                                let lambda_body = self
                                    .bind(lambda_var.clone(), domain, |cxt| {
                                        cxt.check(*lambda_body, codomain)
                                    })
                                    .0?;

                                let depth = lambda_body.depth().inc();
                                return Ok(Term::Tλ(depth, lambda_var, lambda_body.into()));
                            }
                            (raw, expected_type) => (raw, expected_type.into()),
                        }
                }
                let (t, inferred_type) = self.infer(raw)?;

                let lvl = self.lvl;

                self.metas.unify(lvl, expected_type, inferred_type)?;
                Ok(t)
            }
        }
    }

    pub fn close_val(&mut self, value: Value) -> Closure {
        let lvl = self.lvl;
        let quoted_term = value.quote(&mut self.metas, lvl.inc());
        Closure::from(&self.env, quoted_term.into())
    }

    pub fn infer(&mut self, raw: Raw) -> Result<(Term, Rc<Type>), Error> {
        Ok(match raw {
            Raw::RVar(var) => {
                let mut result = Err(());
                for (ix, (var_, r#type)) in self.names.iter().rev().enumerate() {
                    if &var == var_ {
                        result = Ok((Term::TV(Ix(ix)), r#type.clone()));
                        break;
                    }
                }

                result.map_err(|_| error!(ErrorKind::Unbound))?
            }
            Raw::RLam(mut var, term) => {
                let mut inferred_domain = {
                    let meta_domain = self.fresh_meta(Value::VU.into());
                    self.eval(meta_domain)
                };

                let (term, inferred_codomain) = {
                    let (infer_result, (var_, inferred_domain_)) =
                        self.bind(var, inferred_domain, |cxt| cxt.infer(*term));
                    (var, inferred_domain) = (var_, inferred_domain_);
                    infer_result?
                };

                let depth = term.depth().inc();

                (
                    Term::Tλ(depth, var.clone(), term.into()),
                    Type::VΠ(
                        var,
                        inferred_domain,
                        self.close_val(Rc::<Value>::unwrap_or_clone(inferred_codomain)),
                    )
                    .into(),
                )
            }
            Raw::RApp(rator, rand) => {
                let (rator, inferred_rator) = self.infer(*rator)?;
                let (inferred_rator_domain, inferred_rator_codomain) = match self
                    .metas
                    .force(Rc::unwrap_or_clone(inferred_rator))
                {
                    Value::VΠ(_, rator_domain, rator_codomain) => (rator_domain, rator_codomain),
                    inferred_rator => {
                        let mut meta_domain = {
                            let meta_domain = self.fresh_meta(Value::VU.into());
                            self.eval(meta_domain)
                        };
                        let (x, meta_codomain) = {
                            let (meta_codomain, (var_domain, meta_domain_)) =
                                self.bind("a".into(), meta_domain, |cxt| {
                                    cxt.fresh_meta(Value::VU.into())
                                });
                            meta_domain = meta_domain_;
                            (var_domain, Closure::from(&self.env, Rc::new(meta_codomain)))
                        };

                        let lvl = self.lvl;

                        self.metas.unify(
                            lvl,
                            inferred_rator.into(),
                            Value::VΠ(x, meta_domain.clone(), meta_codomain.clone()).into(),
                        )?;
                        (meta_domain, meta_codomain)
                    }
                };
                let checked_rand = self.check(*rand, inferred_rator_domain)?;

                let inferred_type = {
                    let evaluated_rand = self.eval(checked_rand.clone());
                    inferred_rator_codomain.eval(evaluated_rand, &mut self.metas)
                };

                let depth = std::cmp::max(rator.depth().inc(), checked_rand.depth());

                (
                    Term::TApp(depth, rator.into(), checked_rand.into()),
                    inferred_type,
                )
            }
            Raw::RU => (Term::TU, Value::VU.into()),
            Raw::RPi(mut var_domain, domain, codomain) => {
                let checked_domain = self.check(*domain, Value::VU.into())?;
                let checked_codomain = {
                    let evaluated_domain = self.eval(checked_domain.clone());
                    let (check_result, (var_domain_, _)) =
                        self.bind(var_domain, evaluated_domain, |cxt| {
                            cxt.check(*codomain, Value::VU.into())
                        });
                    var_domain = var_domain_;
                    check_result?
                };

                let depth = std::cmp::max(checked_domain.depth(), checked_codomain.depth().inc());

                (
                    Term::TΠ(
                        depth,
                        var_domain,
                        checked_domain.into(),
                        checked_codomain.into(),
                    ),
                    Value::VU.into(),
                )
            }
            Raw::RLet(binder_name, binder_type, binder_def, scope) => {
                let binder_type: Rc<Term> = self.check(*binder_type, Value::VU.into())?.into();
                let v_binder_type = self.eval((*binder_type).clone());

                let binder_def: Rc<Term> = self.check(*binder_def, v_binder_type.clone())?.into();
                let v_binder_def = self.eval((*binder_def).clone());

                let (infer_res, (binder_name, binder_type, _, binder_def, _)) = self.define(
                    binder_name,
                    binder_def,
                    v_binder_def,
                    binder_type,
                    v_binder_type,
                    |cxt| cxt.infer(*scope),
                );

                let (scope, inferred_scope) = infer_res?;

                let depth = std::cmp::max(
                    std::cmp::max(binder_def.depth(), binder_type.depth()),
                    scope.depth().inc(),
                );

                (
                    Term::TLet(depth, binder_name, binder_type, binder_def, scope.into()),
                    inferred_scope,
                )
            }
            Raw::RSrcPos(pos, t) => {
                self.pos = pos;
                self.infer(*t)?
            }
            Raw::RHole => {
                let hole_type = {
                    let m = self.fresh_meta(Value::VU.into());
                    self.eval(m)
                };
                let hole = self.fresh_meta(hole_type.clone());
                (hole, hole_type)
            }
        })
    }

    pub fn normal_form(&mut self, term: Term) -> Term {
        Rc::unwrap_or_clone(self.eval(term)).quote(&mut self.metas, self.env.level())
    }

    fn eval(&mut self, term: Term) -> Rc<Value> {
        let Self { env, metas, .. } = self;

        env.reserve_and_eval(metas, term)
    }

    fn close_type(locals: &[Local], mut ty: Rc<Term>) -> Rc<Term> {
        for local in locals.iter().rev() {
            match local {
                Local::Bound(name, ty_) => {
                    let depth = std::cmp::max(ty.depth().inc(), ty_.depth());
                    ty = Term::TΠ(depth, name.clone(), ty_.clone(), ty).into();
                }
                Local::Defined(x, ty_, def) => {
                    let depth =
                        std::cmp::max(std::cmp::max(ty_.depth(), def.depth()), ty.depth().inc());
                    ty = Term::TLet(depth, x.clone(), ty_.clone(), def.clone(), ty).into();
                }
            }
        }

        ty
    }

    fn fresh_meta(&mut self, ty: VTy) -> Term {
        let Self {
            pruning,
            metas,
            lvl,
            locals,
            ..
        } = self;
        let term = Self::close_type(locals, Rc::unwrap_or_clone(ty).quote(metas, *lvl).into());
        let ty = Env::with_capacity(term.depth().0).eval(metas, Rc::unwrap_or_clone(term));

        metas.fresh_meta_term(ty, pruning.clone())
    }
}
*/
