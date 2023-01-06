#![feature(arc_unwrap_or_clone, allocator_api)]

use std::rc::Rc;

use ast::Ast;
use ::bitvec::vec::BitVec;
use common::Span;
use error::{Error, ErrorKind};
use metas::MetaCxt;
use term::Term;
use value::Value;
use env::Env;




#[macro_use]
pub mod error;
pub mod metas;
pub mod lexer;
pub mod parser;
pub mod raw;
pub mod ast;
pub mod term;
pub mod value;
pub mod env;
pub mod common;

pub use ast::Name;


pub type SourcePos = std::ops::Range<usize>;

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


#[derive(Debug, Clone)]
pub struct Closure<'src>(Env<'src>, Rc<Term<'src>>);

impl<'src> Closure<'src> {
    pub fn from(env: &Env<'src>, term: Rc<Term<'src>>) -> Self {
        let depth = term.depth().0 + 1;
        Self(env.clone_with_capacity(depth), term)
    }

    pub fn eval(self, v: Rc<Value<'src>>, metas: &mut MetaCxt<'src>) -> Rc<Value<'src>> {
        let Closure(mut env, t) = self;
        env.push(v);

        env.eval(metas, Rc::<Term>::unwrap_or_clone(t))
    }
}


#[derive(Debug, Clone)]
pub enum Local<'src> {
    Bound(Name<'src>, Rc<Term<'src>>),
    Defined(Name<'src>, Rc<Term<'src>>, Rc<Term<'src>>),
}

#[derive(Debug, Clone, Default)]
pub struct Cxt<'src> {
    /// used for evaluation
    env: Env<'src>,
    /// used for unification
    lvl: Lvl,
    /// mask of bound variables
    pruning: BitVec<usize>,
    /// getting types of fresh metas
    locals: Vec<Local<'src>>,
    /// names used for lookup during elaboration
    names: Vec<(Name<'src>, Rc<Value<'src>>)>,
    /// used for error reporting
    pos: Span,

    pub metas: MetaCxt<'src>,
}

impl<'src> Cxt<'src> {
    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn lvl(&self) -> Lvl {
        self.lvl
    }

    pub fn bds(&self) -> &Vec<Local> {
        &self.locals
    }

    pub fn pos(&self) -> &Span {
        &self.pos
    }

    #[inline(always)]
    pub fn bind<T>(
        &mut self,
        var_name: Name<'src>,
        v_var_type: Rc<Value<'src>>,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name<'src>, Rc<Value<'src>>)) {
        self.env.push(Value::new_rigid(self.lvl).into());
        let var_type = (*v_var_type).clone().quote(&mut self.metas, self.lvl);

        self.lvl = self.lvl.inc();
        self.locals
            .push(Local::Bound(var_name, var_type.into()));
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
        binder_name: Name<'src>,
        binder_def: Rc<Term<'src>>,
        v_binder_def: Rc<Value<'src>>,
        binder_type: Rc<Term<'src>>,
        v_binder_type: Rc<Value<'src>>,
        scope: impl FnOnce(&mut Self) -> T,
    ) -> (T, (Name<'src>, Rc<Term<'src>>, Rc<Value<'src>>, Rc<Term<'src>>, Rc<Value<'src>>)) {
        self.env.push(v_binder_def);
        self.lvl = self.lvl.inc();

        self.names.push((binder_name, v_binder_type));
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

    pub fn check<'arena>(&mut self, raw: Ast<'src, 'arena>, mut expected_type: Rc<Value<'src>>) -> Result<Term<'src>, Error<'src>>
    where
        'src: 'arena
    {
        match raw {
            Ast::ASrcPos(pos, raw) => {
                self.pos = pos;
                Ok(self.check(*raw, expected_type)?)
            }

            Ast::ALet(binder_name, binder_type, binder_def, scope) => {
                let binder_type: Rc<Term> = match binder_type {
                    Some(binder_type) => self.check(*binder_type, Value::VU.into())?.into(),
                    None => self.fresh_meta(Value::VU.into()).into()
                };
                
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
            Ast::AHole => Ok(self.fresh_meta(expected_type)),

            mut raw => {
                if matches!(&raw, Ast::ALambda(_, _, _)) {
                    (raw, expected_type) =
                        match (raw, self.metas.force(Rc::unwrap_or_clone(expected_type))) {
                            (
                                // TODO lambda var type?
                                Ast::ALambda(lambda_var, _, lambda_body),
                                Value::VΠ(_, domain, codomain),
                            ) => {
                                let codomain = codomain
                                    .eval(Value::new_rigid(self.lvl).into(), &mut self.metas);
                                let lambda_body = self
                                    .bind(lambda_var, domain, |cxt| {
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

    pub fn close_val(&mut self, value: Value<'src>) -> Closure<'src> {
        let lvl = self.lvl;
        let quoted_term = value.quote(&mut self.metas, lvl.inc());
        Closure::from(&self.env, quoted_term.into())
    }

    pub fn infer<'arena>(&mut self, raw: Ast<'src, 'arena>) -> Result<(Term<'src>, Rc<Value<'src>>), Error<'src>> 
    where
        'src: 'arena
    {
        Ok(match raw {
            Ast::AIdent(var) => {
                let mut result = Err(());
                for (ix, (var_, r#type)) in self.names.iter().rev().enumerate() {
                    if matches!(var_, Name::Parsed(_, var)) {
                        result = Ok((Term::TV(Ix(ix)), r#type.clone()));
                        break;
                    }
                }

                result.map_err(|_| error!(ErrorKind::Unbound))?
            }
            // TODO: handle optional type
            Ast::ALambda(mut var, _, term) => {
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
                    Term::Tλ(depth, var, term.into()),
                    Value::VΠ(
                        var,
                        inferred_domain,
                        self.close_val(Rc::<Value>::unwrap_or_clone(inferred_codomain)),
                    )
                    .into(),
                )
            }
            Ast::AApplication(rator, rand) => {
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
                                // TODO: maybe use generated name?
                                self.bind(Name::Elided(None), meta_domain, |cxt| {
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
            Ast::AU => (Term::TU, Value::VU.into()),
            Ast::APi(mut var_domain, domain, codomain) => {
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
            Ast::ALet(binder_name, binder_type, binder_def, scope) => {
                let binder_type: Rc<Term> = match binder_type {
                    Some(binder_type) => self.check(*binder_type, Value::VU.into())?.into(),
                    None => self.fresh_meta(Value::VU.into()).into()
                };
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
            Ast::ASrcPos(pos, t) => {
                self.pos = pos;
                self.infer(*t)?
            }
            Ast::AHole => {
                let hole_type = {
                    let m = self.fresh_meta(Value::VU.into());
                    self.eval(m)
                };
                let hole = self.fresh_meta(hole_type.clone());
                (hole, hole_type)
            }
        })
    }

    pub fn normal_form(&mut self, term: Term<'src>) -> Term<'src> {
        Rc::unwrap_or_clone(self.eval(term)).quote(&mut self.metas, self.env.level())
    }

    fn eval(&mut self, term: Term<'src>) -> Rc<Value<'src>> {
        let Self { env, metas, .. } = self;

        env.reserve_and_eval(metas, term)
    }

    fn close_type(locals: &[Local<'src>], mut ty: Rc<Term<'src>>) -> Rc<Term<'src>> {
        for local in locals.iter().rev() {
            match local {
                Local::Bound(name, ty_) => {
                    let depth = std::cmp::max(ty.depth().inc(), ty_.depth());
                    ty = Term::TΠ(depth, *name, ty_.clone(), ty).into();
                }
                Local::Defined(x, ty_, def) => {
                    let depth =
                        std::cmp::max(std::cmp::max(ty_.depth(), def.depth()), ty.depth().inc());
                    ty = Term::TLet(depth, *x, ty_.clone(), def.clone(), ty).into();
                }
            }
        }

        ty
    }

    fn fresh_meta(&mut self, ty: Rc<Value<'src>>) -> Term<'src> {
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

