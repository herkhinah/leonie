use std::rc::Rc;

use crate::{
    metas::{MetaCxt, MetaVar},
    Closure, Lvl, Name, Term, VTy,
};

#[derive(Debug, Clone, Default)]
pub struct Spine(Vec<Value>);

impl Spine {
    pub fn quote(mut self, metas: &mut MetaCxt, lvl: Lvl, tm: Term) -> Term {
        if let Some(u) = self.0.pop() {
            let rator = self.quote(metas, lvl, tm);
            let rand = u.quote(metas, lvl);
            let depth = std::cmp::max(rator.depth(), rand.depth());

            Term::TApp(depth, rator.into(), rand.into())
        } else {
            tm
        }
    }

    pub fn push(&mut self, value: Rc<Value>) {
        self.0.push(Rc::unwrap_or_clone(value))
    }
}

impl std::iter::IntoIterator for Spine {
    type Item = Value;

    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
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
    // universe
    VU,
}

pub type Type = Value;

#[derive(Debug, Clone)]
struct VFlex(MetaVar, Spine);

#[derive(Debug, Clone)]
struct VRigid(Lvl, Spine);

#[derive(Debug, Clone)]
struct VLambda();

impl Value {
    pub fn quote(self, metas: &mut MetaCxt, lvl: Lvl) -> Term {
        match self {
            Value::VFlex(m, sp) => sp.quote(metas, lvl, Term::TMeta(m)),
            Value::VRigid(x, sp) => sp.quote(metas, lvl, Term::TV(x.as_index(lvl))),
            Value::Vλ(x, clos) => {
                let val = clos.eval(Value::new_rigid(lvl).into(), metas);
                let body = Rc::unwrap_or_clone(val).quote(metas, lvl.inc());
                let depth = body.depth().inc();
                Term::Tλ(depth, x, body.into())
            }
            Value::VΠ(x, a, clos) => {
                let a = Rc::unwrap_or_clone(a).quote(metas, lvl);

                let b = clos.eval(Value::new_rigid(lvl).into(), metas);

                let b = Rc::unwrap_or_clone(b).quote(metas, lvl.inc());

                let depth = std::cmp::max(a.depth(), b.depth().inc());

                Term::TΠ(depth, x, a.into(), b.into())
            }
            Value::VU => Term::TU,
        }
    }

    pub fn app(self, metas: &mut MetaCxt, value: Rc<Value>) -> Rc<Value> {
        match self {
            Value::VFlex(m, mut sp) => {
                sp.push(value);
                Value::VFlex(m, sp).into()
            }
            Value::VRigid(x, mut sp) => {
                sp.push(value);
                Value::VRigid(x, sp).into()
            }
            Value::Vλ(_, clos) => clos.eval(value, metas),
            _ => panic!(),
        }
    }

    pub fn new_flex(m: MetaVar) -> Value {
        Value::VFlex(m, Spine::default())
    }

    pub fn new_rigid(lvl: Lvl) -> Value {
        Value::VRigid(lvl, Spine::default())
    }
}
