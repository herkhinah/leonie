use crate::{
    metas::{MetaCxt, MetaEntry},
    value::Spine,
    Closure, Ix, Lvl, Term, Value,
};
use std::{ops::Index, rc::Rc, slice::Iter};

#[derive(Debug, Clone, Default)]
pub struct Env<'src>(Vec<Rc<Value<'src>>>);

impl<'src> Env<'src> {
    pub fn with_capacity(len: usize) -> Self {
        Self(Vec::with_capacity(len))
    }

    pub fn clone_with_capacity(&self, len: usize) -> Self {
        let mut vec = Vec::with_capacity(self.0.len() + len);
        self.0.clone_into(&mut vec);
        Self(vec)
    }

    pub fn push(&mut self, value: Rc<Value<'src>>) {
        self.0.push(value)
    }

    pub fn pop(&mut self) -> Option<Rc<Value<'src>>> {
        self.0.pop()
    }

    pub fn iter(&self) -> Iter<Rc<Value<'src>>> {
        self.0.iter()
    }

    #[inline(always)]
    pub fn eval_under_binder<T>(
        &mut self,
        value: Rc<Value<'src>>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, Rc<Value<'src>>) {
        self.push(value);
        (f(self), self.pop().unwrap())
    }

    pub fn reserve_and_eval(&mut self, metas: &mut MetaCxt<'src>, term: Term<'src>) -> Rc<Value<'src>> {
        self.0.reserve(term.depth().0);

        self.eval(metas, term)
    }

    pub fn eval(&mut self, metas: &mut MetaCxt<'src>, term: Term<'src>) -> Rc<Value<'src>> {
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

impl<'src> Index<Ix> for Env<'src> {
    type Output = Rc<Value<'src>>;

    fn index(&self, index: Ix) -> &Self::Output {
        &self.0[self.0.len() - 1 - index.0]
    }
}

impl<'src> Index<Lvl> for Env<'src> {
    type Output = Rc<Value<'src>>;

    fn index(&self, index: Lvl) -> &Self::Output {
        &self.0[index.0]
    }
}
