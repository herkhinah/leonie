use std::rc::Rc;

use crate::{
    error::{Error, ErrorKind},
    value::{Spine, Value},
    Env, Lvl, Term, VTy,
};

#[derive(Debug, Clone)]
pub enum MetaEntry {
    Solved(Value, VTy),
    Unsolved(VTy),
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
    pub fn fresh_meta(&mut self, ty: VTy) -> MetaVar {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved(ty));
        m
    }

    pub fn fresh_meta_term(&mut self, ty: VTy, bds: Vec<Option<()>>) -> Term {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved(ty));
        Term::TAppPruning(m, bds)
    }

    pub fn forced_is_var(&self, value: &Value) -> Option<Lvl> {
        match value {
            Value::VFlex(m, sp) if sp.is_empty() => match &self[*m] {
                MetaEntry::Solved(v, _) => self.forced_is_var(v),
                MetaEntry::Unsolved(_) => None,
            },
            Value::VRigid(lvl, sp) if sp.is_empty() => Some(*lvl),
            _ => None,
        }
    }

    pub fn force(&mut self, value: Value) -> Value {
        match value {
            Value::VFlex(m, sp) => match &self[m] {
                MetaEntry::Solved(v, _) => {
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

    pub fn intersect(&mut self, lvl: Lvl, m: MetaVar, sp: Spine, sp_: Spine) -> Result<(), Error> {
        if sp.len() != sp_.len() {
            return Err(error!(ErrorKind::Unify));
        }

        let mut prune = false;

        match sp
            .iter()
            .rev()
            .zip(sp_.iter().rev())
            .map(
                |(t, t_)| match (self.forced_is_var(t), self.forced_is_var(t_)) {
                    (Some(x), Some(x_)) => {
                        if x == x_ {
                            Ok(Some(()))
                        } else {
                            prune = true;
                            Ok(None)
                        }
                    }
                    _ => Err(()),
                },
            )
            .collect::<Result<Vec<Option<()>>, ()>>()
        {
            Ok(pren) => {
                if prune {
                    Prune(pren).prune_meta(self, m).map(|_| ())
                } else {
                    Ok(())
                }
            }
            Err(()) => self.unify_sp(lvl, sp, sp_),
        }
    }

    pub fn unify(&mut self, lvl: Lvl, l: Rc<Value>, r: Rc<Value>) -> Result<(), Error> {
        let l = self.force(Rc::unwrap_or_clone(l));
        let r = self.force(Rc::unwrap_or_clone(r));

        match (l, r) {
            (Value::VU, Value::VU) => Ok(()),
            (Value::VΠ(_, a, b), Value::VΠ(_, a_, b_)) => {
                self.unify(lvl, a, a_)?;
                let b = b.eval(Value::new_rigid(lvl).into(), self);
                let b_ = b_.eval(Value::new_rigid(lvl).into(), self);
                self.unify(lvl.inc(), b, b_)
            }
            (Value::VRigid(x, sp), Value::VRigid(x_, sp_)) if x == x_ => {
                self.unify_sp(lvl, sp, sp_)
            }
            (Value::VFlex(m, sp), Value::VFlex(m_, sp_)) if m == m_ => {
                self.intersect(lvl, m, sp, sp_)
            }
            (Value::VFlex(m, sp), Value::VFlex(m_, sp_)) => self.flex_flex(lvl, (m, sp), (m_, sp_)),

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
            (Value::VFlex(m, sp), t_) => self.solve(lvl, m, sp, t_.into()),
            (t, Value::VFlex(m_, sp_)) => self.solve(lvl, m_, sp_, t.into()),
            (l, r) => Err(error!(ErrorKind::MetaUnify(l, r))),
        }
    }

    pub fn solve(&mut self, lvl: Lvl, m: MetaVar, sp: Spine, rhs: Rc<Value>) -> Result<(), Error> {
        let p_ren = PartialRenaming::invert(self, lvl, &sp)?;
        self.solve_with_pren(m, p_ren, Rc::unwrap_or_clone(rhs))
    }

    pub fn solve_with_pren(
        &mut self,
        m: MetaVar,
        (mut pren, prune_non_linear): (PartialRenaming, Option<Prune<()>>),
        rhs: Value,
    ) -> Result<(), Error> {
        let m_ty = match &self[m] {
            MetaEntry::Solved(_, _) => panic!(),
            MetaEntry::Unsolved(a) => a.clone(),
        };

        if let Some(pr) = prune_non_linear {
            pr.prune_type(self, m_ty.clone())?;
        }

        pren.occ = Some(m);
        let rhs = lams(pren.dom, pren.rename(self, rhs.into())?);
        let depth = rhs.depth();
        let solution = Env::with_capacity(depth.0).eval(self, rhs);
        self[m] = MetaEntry::Solved(Rc::unwrap_or_clone(solution), m_ty);
        Ok(())
    }

    pub fn flex_flex(
        &mut self,
        gamma: Lvl,
        mut left: (MetaVar, Spine),
        mut right: (MetaVar, Spine),
    ) -> Result<(), Error> {
        if left.1.len() < right.1.len() {
            std::mem::swap(&mut left, &mut right);
        }

        let ((m, sp), (m_, sp_)) = (left, right);

        match PartialRenaming::invert(self, gamma, &sp) {
            Err(_) => self.solve(gamma, m_, sp_, Value::VFlex(m, sp).into()),

            Ok(pren) => self.solve_with_pren(m, pren, Value::VFlex(m_, sp_)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    occ: Option<MetaVar>,
    /// size of Δ
    cod: Lvl,
    /// size of Γ
    dom: Lvl,
    /// mapping from Δ vars to Γ vars
    ren: Vec<Option<Lvl>>,
}

impl PartialRenaming {
    pub fn empty() -> Self {
        Self {
            occ: None,
            cod: Lvl(0),
            dom: Lvl(0),
            ren: Vec::new(),
        }
    }

    pub fn lookup(&self, lvl: Lvl) -> Option<Lvl> {
        if lvl.0 < self.ren.len() {
            return self.ren[lvl.0];
        }
        None
    }

    pub fn lift(&mut self) {
        self.ren.push(Some(self.dom));
        self.dom = self.dom.inc();
        self.cod = self.cod.inc();
    }

    pub fn lift_with<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ren.push(Some(self.dom));
        self.dom = self.dom.inc();
        self.cod = self.cod.inc();

        let res = f(self);

        self.dom = self.dom.dec();
        self.cod = self.cod.dec();
        self.ren.pop();

        res
    }

    pub fn skip_with<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ren.push(None);
        self.cod = self.cod.inc();

        let res = f(self);

        self.cod = self.cod.dec();
        self.ren.pop();

        res
    }

    pub fn invert(
        metas: &mut MetaCxt,
        gamma: Lvl,
        spine: &Spine,
    ) -> Result<(Self, Option<Prune<()>>), Error> {
        let mut ren = vec![None; gamma.0 + 1];
        ren.pop();
        let dom = spine.len();

        let mut is_linear = true;
        let mut pr = Vec::with_capacity(spine.len());
        let mut domvars = vec![None; gamma.0];

        for (dom, t) in spine.iter().enumerate() {
            match metas.forced_is_var(t.as_ref()) {
                Some(x) => {
                    if domvars[x.0].is_some() {
                        is_linear = false;
                        ren[x.0] = None;
                        pr.push(None);
                    } else {
                        domvars[x.0] = Some(());
                        ren[x.0] = Some(Lvl(dom));
                        pr.push(Some(()));
                    }
                }
                _ => return Err(error!(ErrorKind::MetaInvert)),
            }
        }

        let pren = if is_linear { None } else { Some(Prune(pr)) };

        Ok((
            PartialRenaming {
                occ: None,

                dom: Lvl(dom),
                cod: gamma,
                ren,
            },
            pren,
        ))
    }

    pub fn rename(&mut self, metas: &mut MetaCxt, v: Rc<Value>) -> Result<Term, Error> {
        match metas.force(Rc::unwrap_or_clone(v)) {
            Value::VFlex(m_, sp) => {
                if let Some(m) = self.occ {
                    if m == m_ {
                        return Err(error!(ErrorKind::MetaOccurs(m, Value::VFlex(m_, sp))));
                    }
                }

                self.prune_vflex(metas, m_, sp)
            }
            Value::VRigid(x, sp) => {
                if self.ren.len() > x.0 {
                    if let Some(x_) = self.ren[x.0] {
                        return self.rename_spine(metas, Term::TV(x_.as_index(self.dom)), sp);
                    }
                }
                Err(error!(ErrorKind::MetaScope(Value::VRigid(x, sp))))
            }
            Value::Vλ(x, t) => {
                let t = t.eval(Value::new_rigid(self.cod).into(), metas);
                let t = self.lift_with(|p_ren| p_ren.rename(metas, t))?;
                let depth = t.depth().inc();
                Ok(Term::Tλ(depth, x, t.into()))
            }
            Value::VΠ(x, a, b) => {
                let a = self.rename(metas, a)?;
                let b = b.eval(Value::new_rigid(self.cod).into(), metas);
                let b = self.lift_with(|p_ren| p_ren.rename(metas, b))?;

                let depth = std::cmp::max(a.depth(), b.depth().inc());

                Ok(Term::TΠ(depth, x, a.into(), b.into()))
            }
            Value::VU => Ok(Term::TU),
        }
    }

    fn rename_spine(&mut self, metas: &mut MetaCxt, mut t: Term, sp: Spine) -> Result<Term, Error> {
        if sp.is_empty() {
            return Ok(t);
        }

        for u in sp.into_iter() {
            let rator = t;
            let rand = self.rename(metas, u)?;

            let depth = std::cmp::max(rator.depth(), rand.depth());

            t = Term::TApp(depth, rator.into(), rand.into());
        }

        Ok(t)
    }

    fn prune_vflex(&mut self, metas: &mut MetaCxt, m: MetaVar, sp: Spine) -> Result<Term, Error> {
        enum PruneStatus {
            OKRenaming,
            OKNonRenaming,
            NeedsPruning,
        }

        let mut status = PruneStatus::OKRenaming;

        let mut pr = Vec::with_capacity(sp.len());
        let mut pruned_spine = Vec::with_capacity(sp.len());

        for t in sp.into_iter().rev() {
            match metas.forced_is_var(t.as_ref()) {
                Some(x) => match (self.lookup(x), &status) {
                    (Some(x), _) => {
                        pr.push(Some(()));
                        pruned_spine.push(Term::TV(x.as_index(self.dom)));
                    }
                    (None, PruneStatus::OKNonRenaming) => return Err(error!(ErrorKind::Unify)),
                    (None, _) => {
                        status = PruneStatus::NeedsPruning;
                        pr.push(None)
                    }
                },
                None => match &status {
                    PruneStatus::NeedsPruning => return Err(error!(ErrorKind::Unify)),
                    _ => {
                        status = PruneStatus::OKNonRenaming;
                        let t = self.rename(metas, t)?;
                        pr.push(Some(()));
                        pruned_spine.push(t);
                    }
                },
            }
        }

        let mut term = match status {
            PruneStatus::OKNonRenaming | PruneStatus::OKRenaming => match metas[m] {
                MetaEntry::Solved(_, _) => return Err(error!(ErrorKind::Unify)),
                MetaEntry::Unsolved(_) => Term::TMeta(m),
            },
            PruneStatus::NeedsPruning => Term::TMeta(Prune(pr).prune_meta(metas, m)?),
        };

        for arg in pruned_spine.into_iter() {
            let depth = std::cmp::max(arg.depth(), term.depth());
            term = Term::TApp(depth, term.into(), arg.into());
        }

        Ok(term)
    }
}

#[derive(Debug)]
pub struct Prune<T>(Vec<Option<T>>);

impl Prune<()> {
    pub fn prune_meta(self, metas: &mut MetaCxt, m: MetaVar) -> Result<MetaVar, Error> {
        let mty = match &metas[m] {
            MetaEntry::Solved(_, _) => panic!(),
            MetaEntry::Unsolved(a) => a.clone(),
        };

        let pruned_tm = self.prune_type(metas, mty.clone())?;
        let depth = pruned_tm.depth();

        let pruned_ty = Env::with_capacity(depth.0).eval(metas, pruned_tm);
        let m_ = metas.fresh_meta(pruned_ty);

        let lvl = Lvl(self.0.len());
        let term = lams(lvl, Term::TAppPruning(m_, self.0));
        let depth = term.depth();

        let solution = Env::with_capacity(depth.0).eval(metas, term);
        metas[m] = MetaEntry::Solved(Rc::unwrap_or_clone(solution), mty);
        Ok(m_)
    }

    pub fn prune_type(&self, metas: &mut MetaCxt, ty: VTy) -> Result<Term, Error> {
        let mut pren = PartialRenaming::empty();

        fn prune(
            pr: &[Option<()>],
            metas: &mut MetaCxt,
            pren: &mut PartialRenaming,
            ty: Rc<Value>,
        ) -> Result<Term, Error> {
            match (pr, metas.force(Rc::unwrap_or_clone(ty))) {
                ([], a) => pren.rename(metas, a.into()),
                ([head @ .., Some(_)], Value::VΠ(x, a, b)) => {
                    let a = pren.rename(metas, a)?;
                    let v = Value::VRigid(pren.cod, Spine::default());
                    let b = b.eval(v.into(), metas);
                    pren.lift_with(|pren| {
                        let b = prune(head, metas, pren, b)?;

                        let depth = std::cmp::max(a.depth(), b.depth());

                        Ok(Term::TΠ(depth, x, a.into(), b.into()))
                    })
                }
                ([head @ .., None], Value::VΠ(_, _, b)) => {
                    let b = b.eval(Value::VRigid(pren.cod, Spine::default()).into(), metas);
                    pren.skip_with(|pren| prune(head, metas, pren, b))
                }
                (pr, a) => panic!("{pr:#?} {a:#?}"),
            }
        }

        prune(&self.0, metas, &mut pren, ty)
    }
}

pub fn lams(lvl: Lvl, mut t: Term) -> Term {
    for i in 0..*lvl {
        let depth = t.depth().inc();
        t = Term::Tλ(depth, format!("x{}", i + 1).into(), t.into());
    }
    t
}

// TODO: in elab-zoo pattern VVar matches on Vrigid with empty spine. Not sure if we check that the spine is empty
