use std::{collections::HashMap as Map, rc::Rc};

use crate::{
    error::{Error, ErrorKind},
    value::{Spine, Value},
    Env, Lvl, Term, BD,
};

#[derive(Debug, Clone)]
pub enum MetaEntry {
    Solved(Value),
    Unsolved,
}

pub type MetaVar = usize;

#[derive(Debug, Clone, Default)]
pub struct MetaCxt(Vec<MetaEntry>);

impl std::ops::Index<MetaVar> for MetaCxt {
    type Output = MetaEntry;

    fn index(&self, index: MetaVar) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::IndexMut<MetaVar> for MetaCxt {
    fn index_mut(&mut self, index: MetaVar) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl MetaCxt {
    pub fn fresh_meta(&mut self, bds: &[BD]) -> Term {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved);
        Term::TInsertedMeta(m, bds.to_vec())
    }

    pub fn force(&mut self, value: Value) -> Value {
        match value {
            Value::VFlex(m, sp) => match &self[m] {
                MetaEntry::Solved(v) => {
                    let mut v = v.clone();

                    for arg in sp.into_iter() {
                        v = Rc::unwrap_or_clone(v.app(self, arg.into()));
                    }

                    v
                }
                _ => Value::VFlex(m, sp),
            },
            other => other,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    /// size of Δ
    cod: Lvl,
    /// size of Γ
    dom: Lvl,
    /// mapping from Δ vars to Γ vars
    ren: Map<Lvl, Lvl>,
}

impl PartialRenaming {
    pub fn lift<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ren.insert(self.cod, self.dom);
        self.dom = self.dom.inc();
        self.cod = self.cod.inc();

        let res = f(self);

        self.dom = self.dom.dec();
        self.cod = self.cod.dec();
        self.ren.remove(&self.cod);

        res
    }

    pub fn invert(metas: &mut MetaCxt, gamma: Lvl, spine: Spine) -> Result<Self, Error> {
        let mut ren = Map::new();
        let dom = spine.len();

        for (dom, t) in spine.iter().cloned().enumerate() {
            match metas.force(t) {
                Value::VRigid(x, y) if !ren.contains_key(&x) && y.is_empty() => {
                    ren.insert(x, Lvl(dom));
                }
                _ => return Err(error!(ErrorKind::MetaInvert(spine))),
            }
        }

        Ok(PartialRenaming {
            dom: Lvl(dom),
            cod: gamma,
            ren,
        })
    }

    fn go(&mut self, metas: &mut MetaCxt, m: MetaVar, v: Rc<Value>) -> Result<Term, Error> {
        match metas.force(Rc::unwrap_or_clone(v)) {
            Value::VFlex(m_, sp) => {
                if m == m_ {
                    return Err(error!(ErrorKind::MetaOccurs(m, Value::VFlex(m_, sp))));
                }

                self.go_sp(metas, m, Term::TMeta(m_), sp)
            }
            Value::VRigid(x, sp) => match self.ren.get(&x) {
                Some(x_) => self.go_sp(metas, m, Term::TV(x_.as_index(self.dom)), sp),
                None => Err(error!(ErrorKind::MetaScope(m, Value::VRigid(x, sp)))),
            },
            Value::Vλ(x, t) => {
                let t = t.eval(Value::new_rigid(self.cod).into(), metas);
                let t = self.lift(|pren| pren.go(metas, m, t))?;
                Ok(Term::Tλ(x, t.into()))
            }
            Value::VΠ(x, a, b) => {
                let a = self.go(metas, m, a)?;
                let b = b.eval(Value::new_rigid(self.cod).into(), metas);
                let b = self.lift(|pren| pren.go(metas, m, b))?;

                Ok(Term::TΠ(x, a.into(), b.into()))
            }
            Value::VU => Ok(Term::TU),
        }
    }

    fn go_sp(
        &mut self,
        metas: &mut MetaCxt,
        m: MetaVar,
        mut t: Term,
        sp: Spine,
    ) -> Result<Term, Error> {
        if sp.is_empty() {
            return Ok(t);
        }

        for u in sp.into_iter() {
            t = Term::TApp(t.into(), self.go(metas, m, u.into())?.into());
        }

        Ok(t)
    }

    pub fn rename(
        self: &mut PartialRenaming,
        metas: &mut MetaCxt,
        m: MetaVar,
        v: Rc<Value>,
    ) -> Result<Term, Error> {
        self.go(metas, m, v)
    }
}

pub fn unify_sp(metas: &mut MetaCxt, lvl: Lvl, sp: Spine, sp_: Spine) -> Result<(), Error> {
    if sp.len() != sp_.len() {
        return Err(error!(ErrorKind::MetaSpine(sp, sp_)));
    }

    for (t, t_) in sp.into_iter().zip(sp_.into_iter()) {
        unify(metas, lvl, t.into(), t_.into())?;
    }

    Ok(())
}

pub fn unify(metas: &mut MetaCxt, lvl: Lvl, l: Rc<Value>, r: Rc<Value>) -> Result<(), Error> {
    let l = metas.force(Rc::unwrap_or_clone(l));
    let r = metas.force(Rc::unwrap_or_clone(r));

    match (l, r) {
        (Value::VU, Value::VU) => Ok(()),
        (Value::Vλ(_, t), Value::Vλ(_, t_)) => {
            let a = t.eval(Value::new_rigid(lvl).into(), metas);
            let b = t_.eval(Value::new_rigid(lvl).into(), metas);

            unify(metas, lvl.inc(), a, b)
        }
        (t, Value::Vλ(_, t_)) => {
            let a = t.app(metas, Value::new_rigid(lvl).into());
            let b = t_.eval(Value::new_rigid(lvl).into(), metas);

            unify(metas, lvl.inc(), a, b)
        }
        (Value::Vλ(_, t), t_) => {
            let a = t.eval(Value::new_rigid(lvl).into(), metas);
            let b = t_.app(metas, Value::new_rigid(lvl).into());

            unify(metas, lvl.inc(), a, b)
        }
        (Value::VΠ(_, a, b), Value::VΠ(_, a_, b_)) => {
            unify(metas, lvl, a, a_)?;
            let b = b.eval(Value::new_rigid(lvl).into(), metas);
            let b_ = b_.eval(Value::new_rigid(lvl).into(), metas);
            unify(metas, lvl.inc(), b, b_)
        }
        (Value::VRigid(x, sp), Value::VRigid(x_, sp_)) if x == x_ => unify_sp(metas, lvl, sp, sp_),
        (Value::VFlex(m, sp), Value::VFlex(m_, sp_)) if m == m_ => unify_sp(metas, lvl, sp, sp_),
        (Value::VFlex(m, sp), t_) => solve(metas, lvl, m, sp, t_.into()),
        (t, Value::VFlex(m_, sp_)) => solve(metas, lvl, m_, sp_, t.into()),
        (l, r) => Err(error!(ErrorKind::MetaUnify(l, r))),
    }
}

pub fn solve(
    metas: &mut MetaCxt,
    lvl: Lvl,
    m: MetaVar,
    sp: Spine,
    v: Rc<Value>,
) -> Result<(), Error> {
    let mut pren = PartialRenaming::invert(metas, lvl, sp)?;
    let rhs = pren.rename(metas, m, v)?;
    let solution = Env::default().eval(metas, lams(pren.dom, rhs));

    metas[m] = MetaEntry::Solved(Rc::unwrap_or_clone(solution));
    Ok(())
}

pub fn lams(lvl: Lvl, mut t: Term) -> Term {
    for i in 0..*lvl {
        t = Term::Tλ(format!("x{}", i + 1).into(), t.into());
    }
    t
}
