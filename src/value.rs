use crate::{
    lvl2ix,
    metas::{MetaCxt, MetaVar},
    Closure, Lvl, Name, Term, VTm, VTy,
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
            Value::VRigid(x, sp) => sp.quote(metas, lvl, Term::TV(lvl2ix(lvl, x))),
            Value::Vλ(x, clos) => {
                let val = clos.eval(metas, Value::new_rigid(lvl));
                Term::Tλ(x, val.quote(metas, lvl + 1).into())
            }
            Value::VΠ(x, a, clos) => {
                let a = a.quote(metas, lvl);

                let b = clos.eval(metas, Value::new_rigid(lvl));

                let b = b.quote(metas, lvl + 1);

                Term::TΠ(x, a.into(), b.into())
            }
            Value::VΣ(_, _, _) => todo!(),
            Value::Vσ(_, _) => todo!(),
            Value::VU => Term::TU,
        }
    }

    pub fn app(self, metas: &mut MetaCxt, value: Value) -> Value {
        match self {
            Value::VFlex(m, mut sp) => {
                sp.push(value);
                Value::VFlex(m, sp)
            }
            Value::VRigid(x, mut sp) => {
                sp.push(value);
                Value::VRigid(x, sp)
            }
            Value::Vλ(_, clos) => clos.eval(metas, value),
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
