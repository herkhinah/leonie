use std::{ops::Index, rc::Rc, slice::Iter};

use crate::{
    metas::{MetaCxt, MetaEntry},
    value::Spine,
    Ix, Local, Lvl, Term, Value,
};

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
            Term::TInsertedMeta(m, bds) => {
                let mut args = Spine::default();

                match &metas[m] {
                    MetaEntry::Solved(val, _) => {
                        let mut val = val.clone();
                        for (t, bds) in self.iter().zip(bds.into_iter()) {
                            if let Local::Bound(_, _) = bds {
                                val = Rc::unwrap_or_clone(val.app(metas, t.clone()));
                            }
                        }
                        val.into()
                    }
                    MetaEntry::Unsolved(_) => {
                        for (t, bds) in self.iter().cloned().zip(bds.into_iter()) {
                            if let Local::Bound(_, _) = bds {
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
