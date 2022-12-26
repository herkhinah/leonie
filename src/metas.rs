use std::rc::Rc;

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
                        v = Rc::unwrap_or_clone(v.app(self, arg));
                    }

                    self.force(v)
                }
                _ => Value::VFlex(m, sp),
            },
            other => other,
        }
    }

    pub fn unify_sp(&mut self, lvl: Lvl, sp: Spine, sp_: Spine) -> Result<(), Error> {
        if sp.len() != sp_.len() {
            return Err(error!(ErrorKind::MetaSpine(sp, sp_)));
        }

        for (t, t_) in sp.into_iter().zip(sp_.into_iter()) {
            self.unify(lvl, t, t_)?;
        }

        Ok(())
    }

    pub fn unify(&mut self, lvl: Lvl, l: Rc<Value>, r: Rc<Value>) -> Result<(), Error> {
        let l = self.force(Rc::unwrap_or_clone(l));
        let r = self.force(Rc::unwrap_or_clone(r));

        match (l, r) {
            (Value::VU, Value::VU) => Ok(()),
            (Value::Vλ(_, t), Value::Vλ(_, t_)) => {
                let a = t.eval(Value::new_rigid(lvl).into(), self);
                let b = t_.eval(Value::new_rigid(lvl).into(), self);

                self.unify(lvl.inc(), a, b)
            }
            (t, Value::Vλ(_, t_)) => {
                let a = t.app(self, Value::new_rigid(lvl).into());
                let b = t_.eval(Value::new_rigid(lvl).into(), self);

                self.unify(lvl.inc(), a, b)
            }
            (Value::Vλ(_, t), t_) => {
                let a = t.eval(Value::new_rigid(lvl).into(), self);
                let b = t_.app(self, Value::new_rigid(lvl).into());

                self.unify(lvl.inc(), a, b)
            }
            (Value::VΠ(_, a, b), Value::VΠ(_, a_, b_)) => {
                self.unify(lvl, a, a_)?;
                let b = b.eval(Value::new_rigid(lvl).into(), self);
                let b_ = b_.eval(Value::new_rigid(lvl).into(), self);
                self.unify(lvl.inc(), b, b_)
            }
            (Value::VRigid(x, sp), Value::VRigid(x_, sp_)) if x == x_ => {
                self.unify_sp(lvl, sp, sp_)
            }
            (Value::VFlex(m, sp), Value::VFlex(m_, sp_)) if m == m_ => self.unify_sp(lvl, sp, sp_),
            (Value::VFlex(m, sp), t_) => self.solve(lvl, m, sp, t_.into()),
            (t, Value::VFlex(m_, sp_)) => self.solve(lvl, m_, sp_, t.into()),
            (l, r) => Err(error!(ErrorKind::MetaUnify(l, r))),
        }
    }

    pub fn solve(&mut self, lvl: Lvl, m: MetaVar, sp: Spine, v: Rc<Value>) -> Result<(), Error> {
        let mut p_ren = PartialRenaming::invert(self, lvl, sp)?;
        let rhs = p_ren.rename(self, m, v)?;
        let lams = lams(p_ren.dom, rhs);
        let solution = Env::with_capacity(lams.depth().0).eval(self, lams);

        self[m] = MetaEntry::Solved(Rc::unwrap_or_clone(solution));
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    /// size of Δ
    cod: Lvl,
    /// size of Γ
    dom: Lvl,
    /// mapping from Δ vars to Γ vars
    ren: Vec<Option<Lvl>>,
}

impl PartialRenaming {
    pub fn lift<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ren.push(Some(self.dom));
        self.dom = self.dom.inc();
        self.cod = self.cod.inc();

        let res = f(self);

        self.dom = self.dom.dec();
        self.cod = self.cod.dec();
        self.ren.pop();

        res
    }

    pub fn invert(metas: &mut MetaCxt, gamma: Lvl, spine: Spine) -> Result<Self, Error> {
        let mut ren = vec![None; gamma.0 + 1];
        ren.pop();
        let dom = spine.len();

        for (dom, t) in spine.into_iter().enumerate() {
            match metas.force(Rc::unwrap_or_clone(t)) {
                Value::VRigid(x, y) if ren[x.0].is_none() && y.is_empty() => {
                    ren[x.0] = Some(Lvl(dom));
                }
                _ => return Err(error!(ErrorKind::MetaInvert)),
            }
        }

        Ok(PartialRenaming {
            dom: Lvl(dom),
            cod: gamma,
            ren,
        })
    }

    pub fn rename(&mut self, metas: &mut MetaCxt, m: MetaVar, v: Rc<Value>) -> Result<Term, Error> {
        match metas.force(Rc::unwrap_or_clone(v)) {
            Value::VFlex(m_, sp) => {
                if m == m_ {
                    return Err(error!(ErrorKind::MetaOccurs(m, Value::VFlex(m_, sp))));
                }

                self.rename_spine(metas, m, Term::TMeta(m_), sp)
            }
            Value::VRigid(x, sp) => {
                if self.ren.len() > x.0 {
                    if let Some(x_) = self.ren[x.0] {
                        return self.rename_spine(metas, m, Term::TV(x_.as_index(self.dom)), sp);
                    }
                }
                Err(error!(ErrorKind::MetaScope(m, Value::VRigid(x, sp))))
            }
            Value::Vλ(x, t) => {
                let t = t.eval(Value::new_rigid(self.cod).into(), metas);
                let t = self.lift(|p_ren| p_ren.rename(metas, m, t))?;
                let depth = t.depth().inc();
                Ok(Term::Tλ(depth, x, t.into()))
            }
            Value::VΠ(x, a, b) => {
                let a = self.rename(metas, m, a)?;
                let b = b.eval(Value::new_rigid(self.cod).into(), metas);
                let b = self.lift(|p_ren| p_ren.rename(metas, m, b))?;

                let depth = std::cmp::max(a.depth(), b.depth().inc());

                Ok(Term::TΠ(depth, x, a.into(), b.into()))
            }
            Value::VU => Ok(Term::TU),
        }
    }

    fn rename_spine(
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
            let rator = t;
            let rand = self.rename(metas, m, u)?;

            let depth = std::cmp::max(rator.depth(), rand.depth());

            t = Term::TApp(depth, rator.into(), rand.into());
        }

        Ok(t)
    }
}

pub fn lams(lvl: Lvl, mut t: Term) -> Term {
    for i in 0..*lvl {
        let depth = t.depth().inc();
        t = Term::Tλ(depth, format!("x{}", i + 1).into(), t.into());
    }
    t
}
