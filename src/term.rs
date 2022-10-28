#[derive(Debug, Clone, Copy)]
pub struct Tm(usize);

#[derive(Debug, Clone, Copy)]
pub struct Ty(usize);

struct TermCxt {
    terms: Vec<Term>,
}

impl TermCxt {
    fn get(&self, tm: Tm) -> Term {
        self.terms[tm.0].clone()
    }
}

type MetaVar = usize;
type Name = usize;

#[derive(Debug, Clone, Copy)]
enum Term {
    TV(Ix),
    Tλ(Name, Tm),
    TΠ(Name, Ty, Ty),
    Tσ(Tm, Tm),
    TΣ(Name, Ty, Ty),
    TLet(Name, Ty, Tm, Tm),
    TMeta(MetaVar),
}
