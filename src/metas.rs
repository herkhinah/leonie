use ::bitvec::vec::BitVec;
use std::rc::Rc;

use crate::{
    error::{Error, ErrorKind},
    value::{Spine, Value},
    Env, Lvl, Term, Name,
};

#[derive(Debug, Clone)]
pub enum MetaEntry<'src> {
    Solved(Value<'src>, Rc<Value<'src>>),
    Unsolved(Rc<Value<'src>>),
}

pub type MetaVar = usize;

#[derive(Debug, Clone, Default)]
pub struct MetaCxt<'src>(Vec<MetaEntry<'src>>);

impl<'src> std::ops::Index<MetaVar> for MetaCxt<'src> {
    type Output = MetaEntry<'src>;

    fn index(&self, index: MetaVar) -> &Self::Output {
        &self.0[index]
    }
}

impl<'src> std::ops::IndexMut<MetaVar> for MetaCxt<'src> {
    fn index_mut(&mut self, index: MetaVar) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<'src> MetaCxt<'src> {
    pub fn fresh_meta(&mut self, ty: Rc<Value<'src>>) -> MetaVar {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved(ty));
        m
    }

    pub fn fresh_meta_term(&mut self, ty: Rc<Value<'src>>, bds: BitVec<usize>) -> Term<'src> {
        let m = self.0.len();
        self.0.push(MetaEntry::Unsolved(ty));
        Term::TAppPruning(m, bds)
    }

    pub fn forced_is_var(&self, value: &Value<'src>) -> Option<Lvl> {
        match value {
            Value::VFlex(m, sp) if sp.is_empty() => match &self[*m] {
                MetaEntry::Solved(v, _) => self.forced_is_var(v),
                MetaEntry::Unsolved(_) => None,
            },
            Value::VRigid(lvl, sp) if sp.is_empty() => Some(*lvl),
            _ => None,
        }
    }

    pub fn force(&mut self, value: Value<'src>) -> Value<'src> {
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

    pub fn unify_sp(&mut self, lvl: Lvl, sp: Spine<'src>, sp_: Spine<'src>) -> Result<(), Error<'src>> {
        if sp.len() != sp_.len() {
            return Err(error!(ErrorKind::MetaSpine(sp, sp_)));
        }

        for (t, t_) in sp.into_iter().zip(sp_.into_iter()) {
            self.unify(lvl, t, t_)?;
        }

        Ok(())
    }

    pub fn intersect(&mut self, lvl: Lvl, m: MetaVar, sp: Spine<'src>, sp_: Spine<'src>) -> Result<(), Error<'src>> {
        if sp.len() != sp_.len() {
            return Err(error!(ErrorKind::Unify));
        }

        let mut prune = Ok(false);
        let mut pr = BitVec::new();

        for (t, t_) in sp.iter().rev().zip(sp_.iter().rev()) {
            match (self.forced_is_var(t), self.forced_is_var(t_)) {
                (Some(x), Some(x_)) => {
                    if x == x_ {
                        pr.push(true);
                    } else {
                        prune = Ok(true);
                        pr.push(false);
                    }
                }
                _ => {
                    prune = Err(());
                    break;
                }
            }
        }
        match prune {
            Ok(pren) => {
                if pren {
                    Prune(pr).prune_meta(self, m).map(|_| ())
                } else {
                    Ok(())
                }
            }
            Err(()) => self.unify_sp(lvl, sp, sp_),
        }
    }

    pub fn unify(&mut self, lvl: Lvl, l: Rc<Value<'src>>, r: Rc<Value<'src>>) -> Result<(), Error<'src>> {
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

    pub fn solve(&mut self, lvl: Lvl, m: MetaVar, sp: Spine<'src>, rhs: Rc<Value<'src>>) -> Result<(), Error<'src>> {
        let p_ren = PartialRenaming::invert(self, lvl, &sp)?;
        self.solve_with_pren(m, p_ren, Rc::unwrap_or_clone(rhs))
    }

    pub fn solve_with_pren(
        &mut self,
        m: MetaVar,
        (mut pren, prune_non_linear): (PartialRenaming, Option<Prune>),
        rhs: Value<'src>,
    ) -> Result<(), Error<'src>> {
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
        mut left: (MetaVar, Spine<'src>),
        mut right: (MetaVar, Spine<'src>),
    ) -> Result<(), Error<'src>> {
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

    #[inline(always)]
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

    #[inline(always)]
    pub fn skip_with<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ren.push(None);
        self.cod = self.cod.inc();

        let res = f(self);

        self.cod = self.cod.dec();
        self.ren.pop();

        res
    }

    pub fn invert<'src>(
        metas: &mut MetaCxt<'src>,
        gamma: Lvl,
        spine: &Spine<'src>,
    ) -> Result<(Self, Option<Prune>), Error<'src>> {
        let mut ren = vec![None; gamma.0 + 1];
        ren.pop();
        let dom = spine.len();

        let mut is_linear = true;
        let mut pr = BitVec::with_capacity(spine.len());
        let mut domvars = vec![None; gamma.0];

        for (dom, t) in spine.iter().enumerate() {
            match metas.forced_is_var(t.as_ref()) {
                Some(x) => {
                    if domvars[x.0].is_some() {
                        is_linear = false;
                        ren[x.0] = None;
                        pr.push(false);
                    } else {
                        domvars[x.0] = Some(());
                        ren[x.0] = Some(Lvl(dom));
                        pr.push(true);
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

    pub fn rename<'src>(&mut self, metas: &mut MetaCxt<'src>, v: Rc<Value<'src>>) -> Result<Term<'src>, Error<'src>> {
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

    #[inline(always)]
    fn rename_spine<'src>(&mut self, metas: &mut MetaCxt<'src>, mut t: Term<'src>, sp: Spine<'src>) -> Result<Term<'src>, Error<'src>> {
        if sp.is_empty() {
            return Ok(t);
        }

        for u in sp.into_iter() {
            let rator = t;
            let rand = self.rename(metas, u)?;

            let depth = std::cmp::max(rator.depth().inc(), rand.depth());

            t = Term::TApp(depth, rator.into(), rand.into());
        }

        Ok(t)
    }

    fn prune_vflex<'src>(&mut self, metas: &mut MetaCxt<'src>, m: MetaVar, sp: Spine<'src>) -> Result<Term<'src>, Error<'src>> {
        enum PruneStatus {
            OKRenaming,
            OKNonRenaming,
            NeedsPruning,
        }

        let mut status = PruneStatus::OKRenaming;

        let mut pr = BitVec::with_capacity(sp.len());
        let mut pruned_spine = Vec::with_capacity(sp.len());

        for t in sp.into_iter().rev() {
            match metas.forced_is_var(t.as_ref()) {
                Some(x) => match (self.lookup(x), &status) {
                    (Some(x), _) => {
                        pr.push(true);
                        pruned_spine.push(Term::TV(x.as_index(self.dom)));
                    }
                    (None, PruneStatus::OKNonRenaming) => return Err(error!(ErrorKind::Unify)),
                    (None, _) => {
                        status = PruneStatus::NeedsPruning;
                        pr.push(false)
                    }
                },
                None => match &status {
                    PruneStatus::NeedsPruning => return Err(error!(ErrorKind::Unify)),
                    _ => {
                        status = PruneStatus::OKNonRenaming;
                        let t = self.rename(metas, t)?;
                        pr.push(true);
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
            let depth = std::cmp::max(arg.depth(), term.depth().inc());
            term = Term::TApp(depth, term.into(), arg.into());
        }

        Ok(term)
    }

    pub(crate) fn skip(&mut self) {
        self.ren.push(None);
        self.cod = self.cod.inc();
    }
}

#[derive(Debug, Clone)]
pub struct Prune(BitVec<usize>);

impl Prune {
    pub fn prune_meta<'src>(self, metas: &mut MetaCxt<'src>, m: MetaVar) -> Result<MetaVar, Error<'src>> {
        let mty = match &metas[m] {
            MetaEntry::Solved(_, _) => panic!(),
            MetaEntry::Unsolved(a) => a.clone(),
        };

        let pruned_tm = self.clone().prune_type(metas, mty.clone())?;
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

    pub fn prune_type<'src>(mut self, metas: &mut MetaCxt<'src>, ty: Rc<Value<'src>>) -> Result<Term<'src>, Error<'src>> {
        let mut pren = PartialRenaming::empty();

        fn prune<'src>(
            pr: &mut BitVec<usize>,
            metas: &mut MetaCxt<'src>,
            pren: &mut PartialRenaming,
            mut ty: Rc<Value<'src>>,
        ) -> Result<Term<'src>, Error<'src>> {
            let mut vec = Vec::with_capacity(pr.len());

            for prune in pr.iter().by_vals() {
                match (prune, metas.force(Rc::unwrap_or_clone(ty))) {
                    (true, Value::VΠ(x, a, b)) => {
                        let a = pren.rename(metas, a)?;
                        let v = Value::VRigid(pren.cod, Spine::default());
                        vec.push((x, a));
                        ty = b.eval(v.into(), metas);
                        pren.lift();
                    }
                    (false, Value::VΠ(_, _, b)) => {
                        ty = b.eval(Value::VRigid(pren.cod, Spine::default()).into(), metas);
                        pren.skip();
                    }
                    _ => panic!(),
                }
            }

            let mut term = pren.rename(metas, ty)?;

            for (name, ty) in vec.into_iter().rev() {
                let depth = std::cmp::max(ty.depth(), term.depth().inc());
                term = Term::TΠ(depth, name, ty.into(), term.into());
            }

            Ok(term)
        }

        prune(&mut self.0, metas, &mut pren, ty)
    }
}

pub fn lams<'src>(lvl: Lvl, mut t: Term<'src>) -> Term<'src> {
    for i in 0..*lvl {
        let depth = t.depth().inc();
        t = Term::Tλ(depth, Name::Generated(i), t.into());
    }
    t
}

// TODO: in elab-zoo pattern VVar matches on Vrigid with empty spine. Not sure if we check that the spine is empty
