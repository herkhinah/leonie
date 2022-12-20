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
            Term::TApp(
                self.quote(metas, lvl, tm).into(),
                u.quote(metas, lvl).into(),
            )
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
                Term::Tλ(x, Rc::unwrap_or_clone(val).quote(metas, lvl.inc()).into())
            }
            Value::VΠ(x, a, clos) => {
                let a = Rc::unwrap_or_clone(a).quote(metas, lvl);

                let b = clos.eval(Value::new_rigid(lvl).into(), metas);

                let b = Rc::unwrap_or_clone(b).quote(metas, lvl.inc());

                Term::TΠ(x, a.into(), b.into())
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
