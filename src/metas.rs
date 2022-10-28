use std::collections::HashMap as Map;
use std::{backtrace::Backtrace, borrow::Cow};

use crate::{eval, eval_closure, lvl2ix, v_app, Cxt, Env, Lvl, Spine, Term, Value};

#[derive(Debug)]
pub struct Error {
    pub backtrace: Backtrace,
    pub kind: ErrorKind,
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    MetaOccurs(MetaVar, Value),
    MetaScope(MetaVar, Value),
    MetaSpine(Spine, Spine),
    MetaInvert(Spine),
    MetaUnify(Value, Value),
    InferUnbound(),
}

macro_rules! error {
    ($error_kind:expr) => {
        Err(Error {
            backtrace: Backtrace::capture(),
            kind: $error_kind,
        })
    };
}

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
    pub fn fresh_meta(&mut self, cxt: &Cxt) -> Term {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved);
        Term::TInsertedMeta(m, cxt.bds.clone())
    }

    pub fn force(&self, v: Value) -> Value {
        match v {
            Value::VFlex(m, sp) => match &self[m] {
                MetaEntry::Solved(v) => v.clone(),
                MetaEntry::Unsolved => Value::VFlex(m, sp),
            },
            v => v,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    /// size of Γ
    cod: Lvl,
    /// size of Δ
    dom: Lvl,
    /// mapping from Δ vars to Γ vars
    ren: Map<Lvl, Lvl>,
}

impl PartialRenaming {
    pub fn lift(&mut self) {
        self.ren.insert(self.cod, self.dom);
        self.dom += 1;
        self.cod += 1;
    }

    pub fn unlift(&mut self) {
        self.dom -= 1;
        self.cod -= 1;
        self.ren.remove(&self.cod);
    }

    pub fn invert(metas: &MetaCxt, gamma: Lvl, spine: Spine) -> Result<Self, Error> {
        let mut ren = Map::new();
        let dom = spine.len();

        for (dom, t) in spine.iter().cloned().enumerate() {
            match metas.force(t) {
                Value::VRigid(x, y) if !ren.contains_key(&x) && y.is_empty() => {
                    ren.insert(x, dom);
                }
                _ => return error!(ErrorKind::MetaInvert(spine)),
            }
        }

        Ok(PartialRenaming {
            dom,
            cod: gamma,
            ren,
        })
    }
}

pub fn rename(
    mcxt: &mut MetaCxt,
    m: MetaVar,
    pren: &mut PartialRenaming,
    v: Value,
) -> Result<Term, Error> {
    fn go(
        metas: &mut MetaCxt,
        m: MetaVar,
        pren: &mut PartialRenaming,
        v: Value,
    ) -> Result<Term, Error> {
        match metas.force(v) {
            Value::VFlex(m_, sp) => {
                if m == m_ {
                    return error!(ErrorKind::MetaOccurs(m, Value::VFlex(m_, sp)));
                }

                go_sp(metas, m, pren, Term::TMeta(m_), sp)
            }
            Value::VRigid(x, sp) => match pren.ren.get(&x) {
                Some(x_) => go_sp(metas, m, pren, Term::TV(lvl2ix(pren.dom, *x_)), sp),
                None => error!(ErrorKind::MetaScope(m, Value::VRigid(x, sp))),
            },
            Value::Vλ(x, t) => {
                let t = eval_closure(metas, t, Value::VRigid(pren.cod, vec![]));
                pren.lift();
                let t = go(metas, m, pren, t);
                pren.unlift();

                Ok(Term::Tλ(x, t?.into()))
            }
            Value::VΠ(x, a, b) => {
                let a = go(metas, m, pren, *a)?;
                let b = eval_closure(metas, b, Value::VRigid(pren.cod, vec![]));
                pren.lift();
                let b = go(metas, m, pren, b);
                pren.unlift();

                Ok(Term::TΠ(x, a.into(), b?.into()))
            }
            Value::VΣ(_, _, _) => todo!(),
            Value::Vσ(_, _) => todo!(),
            Value::VU => Ok(Term::TU),
        }
    }

    fn go_sp(
        mcxt: &mut MetaCxt,
        m: MetaVar,
        pren: &mut PartialRenaming,
        mut t: Term,
        sp: Spine,
    ) -> Result<Term, Error> {
        if sp.is_empty() {
            return Ok(t);
        }

        for u in sp.into_iter() {
            t = Term::TApp(t.into(), go(mcxt, m, pren, u)?.into());
        }

        Ok(t)
    }

    go(mcxt, m, pren, v)
}

pub fn unify_sp(mcxt: &mut MetaCxt, lvl: Lvl, mut sp: Spine, mut sp_: Spine) -> Result<(), Error> {
    match (sp.pop(), sp_.pop()) {
        (None, None) => Ok(()),
        (Some(t), Some(t_)) => {
            unify_sp(mcxt, lvl, sp, sp_)?;
            unify(mcxt, lvl, t, t_)
        }
        _ => error!(ErrorKind::MetaSpine(sp, sp_)),
    }
}

pub fn unify(mcxt: &mut MetaCxt, lvl: Lvl, l: Value, r: Value) -> Result<(), Error> {
    let l = mcxt.force(l);
    let r = mcxt.force(r);

    match (l, r) {
        (Value::VU, Value::VU) => Ok(()),
        (Value::Vλ(_, t), Value::Vλ(_, t_)) => {
            let a = eval_closure(mcxt, t, Value::VRigid(lvl, vec![]));
            let b = eval_closure(mcxt, t_, Value::VRigid(lvl, vec![]));

            unify(mcxt, lvl + 1, a, b)
        }
        (t, Value::Vλ(_, t_)) => {
            let a = v_app(mcxt, t, Value::VRigid(lvl, vec![]));
            let b = eval_closure(mcxt, t_, Value::VRigid(lvl, vec![]));

            unify(mcxt, lvl + 1, a, b)
        }
        (Value::Vλ(_, t), t_) => {
            let a = eval_closure(mcxt, t, Value::VRigid(lvl, vec![]));
            let b = v_app(mcxt, t_, Value::VRigid(lvl, vec![]));

            unify(mcxt, lvl + 1, a, b)
        }
        (Value::VΠ(_, a, b), Value::VΠ(_, a_, b_)) => {
            unify(mcxt, lvl, *a, *a_)?;
            let b = eval_closure(mcxt, b, Value::VRigid(lvl, vec![]));
            let b_ = eval_closure(mcxt, b_, Value::VRigid(lvl, vec![]));
            unify(mcxt, lvl + 1, b, b_)
        }
        (Value::VRigid(x, sp), Value::VRigid(x_, sp_)) if x == x_ => unify_sp(mcxt, lvl, sp, sp_),
        (Value::VFlex(m, sp), Value::VFlex(m_, sp_)) if m == m_ => unify_sp(mcxt, lvl, sp, sp_),
        (Value::VFlex(m, sp), t_) => solve(mcxt, lvl, m, sp, t_),
        (t, Value::VFlex(m_, sp_)) => solve(mcxt, lvl, m_, sp_, t),
        (l, r) => {
            error!(ErrorKind::MetaUnify(l, r))
        }
    }
}

pub fn solve(metas: &mut MetaCxt, lvl: Lvl, m: MetaVar, sp: Spine, v: Value) -> Result<(), Error> {
    let pren = PartialRenaming::invert(metas, lvl, sp)?;
    let rhs = rename(metas, m, &mut pren.clone(), v)?;
    let solution = eval(metas, Cow::Owned(Env::default()), lams(pren.dom, rhs));

    metas[m] = MetaEntry::Solved(solution);
    Ok(())
}

pub fn lams(lvl: Lvl, mut t: Term) -> Term {
    for i in 0..lvl {
        t = Term::Tλ(format!("x{}", i + 1).into(), t.into());
    }
    t
}
