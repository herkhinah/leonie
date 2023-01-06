use std::rc::Rc;

use crate::{
    metas::{MetaCxt, MetaVar},
    Closure, Lvl, Name, Term,
};

#[derive(Debug, Clone, Default)]
pub struct Spine<'src>(Vec<Rc<Value<'src>>>);

impl<'src> Spine<'src> {
    pub fn quote(mut self, metas: &mut MetaCxt<'src>, lvl: Lvl, tm: Term<'src>) -> Term<'src> {
        if let Some(u) = self.0.pop() {
            let rator = self.quote(metas, lvl, tm);
            let rand = Rc::unwrap_or_clone(u).quote(metas, lvl);
            let depth = std::cmp::max(rator.depth().inc(), rand.depth());

            Term::TApp(depth, rator.into(), rand.into())
        } else {
            tm
        }
    }

    pub fn push(&mut self, value: Rc<Value<'src>>) {
        self.0.push(value)
    }
}

impl<'src> std::iter::IntoIterator for Spine<'src> {
    type Item = Rc<Value<'src>>;

    type IntoIter = std::vec::IntoIter<Rc<Value<'src>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'src> std::ops::Deref for Spine<'src> {
    type Target = Vec<Rc<Value<'src>>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum Value<'src> {
    /// unsolved meta variabel
    VFlex(MetaVar, Spine<'src>),
    /// bound variable applied to zero or more arguments
    VRigid(Lvl, Spine<'src>),
    // lambda closure
    Vλ(Name<'src>, Closure<'src>),
    // pi type
    VΠ(Name<'src>, Rc<Self>, Closure<'src>),
    // universe
    VU,
}


#[derive(Debug, Clone)]
struct VFlex<'src>(MetaVar, Spine<'src>);

#[derive(Debug, Clone)]
struct VRigid<'src>(Lvl, Spine<'src>);

#[derive(Debug, Clone)]
struct VLambda();

impl<'src> Value<'src> {
    pub fn quote(self, metas: &mut MetaCxt<'src>, lvl: Lvl) -> Term<'src> {
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

    pub fn app(self, metas: &mut MetaCxt<'src>, value: Rc<Value<'src>>) -> Rc<Value<'src>> {
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

    pub fn new_flex(m: MetaVar) -> Value<'src> {
        Value::VFlex(m, Spine::default())
    }

    pub fn new_rigid(lvl: Lvl) -> Value<'src> {
        Value::VRigid(lvl, Spine::default())
    }
}
