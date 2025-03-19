use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::ren::Ren;
use crate::rep::Rep;
use crate::syntax::{Id, Mult, SId, SType, Session, SessionB, SessionO, SessionOp, Type};
use crate::util::boxed::Boxed;
use crate::util::graph::Graph;
use crate::util::pretty::{Pretty, PrettyEnv};
use crate::util::span::fake_span;

use CtxCtxS::*;
use CtxS::*;
use JoinOrd::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinOrd {
    Ordered,
    Unordered,
}

impl Mult {
    pub fn to_join_ord(&self) -> JoinOrd {
        match self {
            Mult::Unr => JoinOrd::Ordered,
            Mult::Lin => JoinOrd::Unordered,
            Mult::OrdL => JoinOrd::Ordered,
            Mult::OrdR => JoinOrd::Ordered,
        }
    }
    pub fn choose_ctxs<'a>(&self, c1: &'a Ctx, c2: &'a Ctx) -> (&'a Ctx, &'a Ctx) {
        match self {
            Mult::OrdR => (c2, c1),
            _ => (c1, c2),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Ctx {
    Empty,
    Bind(SId, SType),
    Join(Box<Ctx>, Box<Ctx>, JoinOrd),
}

#[allow(non_snake_case)]
pub mod CtxS {
    use super::*;

    #[allow(non_upper_case_globals)]
    pub const Empty: Ctx = Ctx::Empty;

    pub fn Bind(x: SId, t: SType) -> Ctx {
        Ctx::Bind(x, t)
    }

    pub fn Join(c1: impl Boxed<Ctx>, c2: impl Boxed<Ctx>, o: JoinOrd) -> Ctx {
        Ctx::Join(c1.boxed(), c2.boxed(), o)
    }
}

pub fn ext(m: Mult, c1: Ctx, c2: Ctx) -> Ctx {
    match m {
        Mult::Unr => CtxS::Join(c1, c2, JoinOrd::Ordered),
        Mult::Lin => CtxS::Join(c1, c2, JoinOrd::Unordered),
        Mult::OrdL => CtxS::Join(c1, c2, JoinOrd::Ordered),
        Mult::OrdR => CtxS::Join(c2, c1, JoinOrd::Ordered),
    }
}

impl Ctx {
    pub fn map_binds(&self, f: &mut impl FnMut(&Id, &Type)) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => f(x, t),
            Ctx::Join(c1, c2, _o) => {
                c1.map_binds(f);
                c2.map_binds(f);
            }
        }
    }
    pub fn map_binds_mut(&mut self, f: &mut impl FnMut(&mut Id, &mut Type)) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => f(x, t),
            Ctx::Join(c1, c2, _o) => {
                c1.map_binds_mut(f);
                c2.map_binds_mut(f);
            }
        }
    }
    pub fn flatmap_binds_mut(&mut self, f: &mut impl FnMut(Id, Type) -> Ctx) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => *self = f(x.val.clone(), t.val.clone()),
            Ctx::Join(c1, c2, _o) => {
                c1.flatmap_binds_mut(f);
                c2.flatmap_binds_mut(f);
            }
        }
    }
    pub fn flatmap_binds(&self, f: &mut impl FnMut(Id, Type) -> Ctx) -> Ctx {
        let mut ctx = self.clone();
        ctx.flatmap_binds_mut(f);
        ctx
    }
    pub fn is_unr(&self) -> bool {
        let mut unr = true;
        self.map_binds(&mut |_x, t| unr = unr && t.is_unr());
        unr
    }
    pub fn lookup_ord_pure(&self, x: &Id) -> Option<(Ctx, SType)> {
        let mut c = self.clone();
        c.lookup_ord(x).map(|t| (c, t))
    }
    pub fn lookup_ord(&mut self, x: &Id) -> Option<SType> {
        match self {
            Ctx::Empty => None,
            Ctx::Bind(y, t) if x == &y.val => {
                if t.is_ord() {
                    let t = t.clone();
                    *self = Ctx::Empty;
                    Some(t)
                } else {
                    Some(t.clone())
                }
            }
            Ctx::Bind(_y, _t) => None,
            Ctx::Join(c1, c2, o) => c1.lookup_ord(x).or_else(|| {
                if c1.is_unr() || *o == JoinOrd::Ordered {
                    c2.lookup_ord(x)
                } else {
                    None
                }
            }),
        }
    }

    pub fn restrict(&self, xs: &HashSet<Id>) -> Self {
        match self {
            Ctx::Empty => Ctx::Empty,
            Ctx::Bind(x, t) if xs.contains(&x.val) => Ctx::Bind(x.clone(), t.clone()),
            Ctx::Bind(_, _) => Ctx::Empty,
            Ctx::Join(c1, c2, o) => CtxS::Join(c1.restrict(xs), c2.restrict(xs), *o),
        }
    }

    pub fn vars(&self) -> HashSet<Id> {
        let mut res = HashSet::new();
        self.map_binds(&mut |x, _t| {
            res.insert(x.clone());
        });
        res
    }
    pub fn lin_vars(&self) -> HashSet<Id> {
        let mut res = HashSet::new();
        self.map_binds(&mut |x, t| {
            if !t.is_unr() {
                res.insert(x.clone());
            }
        });
        res
    }
    pub fn binds(&self) -> HashMap<Id, Type> {
        let mut res = HashMap::new();
        self.map_binds(&mut |x, t| {
            res.insert(x.clone(), t.clone());
        });
        res
    }
    pub fn to_sem(&self) -> SemCtx {
        match self {
            Ctx::Empty => SemCtx::empty(),
            Ctx::Bind(x, t) => SemCtx::bind(x.val.clone(), t.val.clone()),
            Ctx::Join(c1, c2, o) => c1.to_sem().join(&c2.to_sem(), *o),
        }
    }
    pub fn is_splittable(&self, xs: &HashSet<Id>) -> bool {
        let sem = self.to_sem();
        let (binds_xs, binds_not_xs) = self
            .binds()
            .into_iter()
            .filter(|(_, t)| !t.is_unr())
            .partition::<HashSet<_>, _>(|(x, _)| xs.contains(x));
        for b1 in &binds_xs {
            for b2 in &binds_not_xs {
                if sem.ord.is_reachable(b1, b2) {
                    for b3 in &binds_xs {
                        if sem.ord.is_reachable(b2, b3) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
    pub fn split(&self, xs: &HashSet<Id>) -> Option<(CtxCtx, Ctx)> {
        match self {
            Ctx::Empty => Some((CtxCtxS::Hole, Ctx::Empty)),
            Ctx::Bind(x, t) => {
                if !xs.contains(&x.val) {
                    Some((
                        CtxCtxS::JoinL(CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone()), Unordered),
                        Ctx::Empty,
                    ))
                } else if t.is_ord() {
                    Some((CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone())))
                } else {
                    Some((
                        CtxCtxS::JoinL(CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone()), Unordered),
                        Ctx::Bind(x.clone(), t.clone()),
                    ))
                }
            }
            Ctx::Join(c1, c2, o) => {
                if xs.is_disjoint(&c1.vars()) {
                    let (cc, c) = c2.split(xs)?;
                    return Some((CtxCtxS::JoinR(c1.clone(), cc, *o), c));
                } else if xs.is_disjoint(&c2.vars()) {
                    let (cc, c) = c1.split(xs)?;
                    return Some((CtxCtxS::JoinL(cc, c2.clone(), *o), c));
                }
                let (cc1, c1) = c1.split(xs)?;
                let (cc2, c2) = c2.split(xs)?;
                match o {
                    Ordered => {
                        if let (Some(c1x), Some(c2x)) = (cc1.pull_right(), cc2.pull_left()) {
                            Some((
                                JoinR(c1x, JoinL(Hole, c2x, Ordered), Ordered),
                                Join(c1, c2, Ordered),
                            ))
                        } else {
                            None
                        }
                    }
                    Unordered => {
                        if let (Some(c1x), Some(c2x)) = (cc1.pull_par(), cc2.pull_par()) {
                            Some((
                                JoinR(c1x, JoinL(CtxCtxS::Hole, c2x, Unordered), Unordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) = (cc1.pull_right(), cc2.pull_right())
                        {
                            Some((
                                JoinR(Join(c1x, c2x, Unordered), CtxCtxS::Hole, Ordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) = (cc1.pull_left(), cc2.pull_left()) {
                            Some((
                                JoinL(CtxCtxS::Hole, Join(c1x, c2x, Unordered), Ordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) = (cc1.pull_left(), cc2.pull_right()) {
                            Some((
                                JoinR(c2x, JoinL(CtxCtxS::Hole, c1x, Ordered), Ordered),
                                Join(c1, c2, Ordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) = (cc1.pull_right(), cc2.pull_left()) {
                            Some((
                                JoinR(c1x, JoinL(CtxCtxS::Hole, c2x, Ordered), Ordered),
                                Join(c2, c1, Ordered),
                            ))
                        } else {
                            let ((c11, c12), (c21, c22)) = (cc1.pull_closed(), cc2.pull_closed());
                            Some((
                                JoinR(
                                    Join(c11, c21, Unordered),
                                    JoinL(Hole, Join(c12, c22, Unordered), Ordered),
                                    Ordered,
                                ),
                                Join(c1, c2, Unordered),
                            ))
                        }
                    }
                }
            }
        }
    }
    pub fn simplify(&self) -> Self {
        match self {
            Ctx::Empty => Ctx::Empty,
            Ctx::Bind(x, t) => Ctx::Bind(x.clone(), t.clone()),
            Ctx::Join(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (c1, Ctx::Empty) => c1,
                (Ctx::Empty, c2) => c2,
                (c1, c2) => CtxS::Join(c1, c2, *o),
            },
        }
    }
    pub fn is_subctx_of(&self, other: &Self) -> bool {
        self.to_sem().is_subctx_of(&other.to_sem())
    }

    // ⋯ʳ operator from Agda
    pub fn replace(&self, u: &Rep) -> Ctx {
        let mut ctx = self.clone();
        ctx.map_binds_mut(&mut |x: &mut Id, t: &mut Type| {
            if let Type::Chan(_) = &t {
                if let Some(s) = u.map.get(x) {
                    *t = Type::Chan(fake_span(s.clone()));
                }
            }
        });
        ctx
    }

    // %ᶜ operator from Agda
    pub fn split_off(&self, u: &Rep) -> Ctx {
        let mut ctx = self.clone();
        ctx.map_binds_mut(&mut |x: &mut Id, t: &mut Type| {
            if let Type::Chan(s) = &t {
                if let Some(Session::Borrowed(s1)) = u.map.get(x) {
                    if let Some(s2) = s.split(&s1) {
                        *t = Type::Chan(fake_span(s2.clone()));
                    }
                }
            }
        });
        ctx
    }

    // ⋯ᵘ operator from Agda
    pub fn rename(&self, r: &Ren) -> Ctx {
        let mut ctx = self.clone();
        ctx.map_binds_mut(&mut |x: &mut Id, _: &mut Type| {
            if let Some(y) = r.map.get(x) {
                *x = y.clone();
            }
        });
        ctx
    }

    // split-ctx function from Agda
    pub fn split_ctx(&self, sis: &HashMap<Id, SessionB>, r1: &Ren, r2: &Ren) -> Ctx {
        self.flatmap_binds(&mut |x, t| {
            if let Some(s1) = sis.get(&x) {
                if let Type::Chan(s) = &t {
                    if let Some(s2) = s.split(s1) {
                        let s1 = Session::Borrowed(fake_span(s1.clone()));
                        return Ctx::Join(
                            Box::new(Ctx::Bind(
                                fake_span(r1.map.get(&x).unwrap().clone()),
                                fake_span(Type::Chan(fake_span(s1))),
                            )),
                            Box::new(Ctx::Bind(
                                fake_span(r2.map.get(&x).unwrap().clone()),
                                fake_span(Type::Chan(fake_span(s2))),
                            )),
                            JoinOrd::Ordered,
                        );
                    }
                }
            }
            Ctx::Bind(fake_span(x), fake_span(t))
        })
    }
}

#[derive(Debug, Clone)]
pub enum CtxCtx {
    Hole,
    JoinL(Box<CtxCtx>, Box<Ctx>, JoinOrd),
    JoinR(Box<Ctx>, Box<CtxCtx>, JoinOrd),
}

#[allow(non_snake_case)]
pub mod CtxCtxS {
    use super::*;

    #[allow(non_upper_case_globals)]
    pub const Hole: CtxCtx = CtxCtx::Hole;

    pub fn JoinL(cc: impl Boxed<CtxCtx>, c: impl Boxed<Ctx>, o: JoinOrd) -> CtxCtx {
        CtxCtx::JoinL(cc.boxed(), c.boxed(), o)
    }

    pub fn JoinR(c: impl Boxed<Ctx>, cc: impl Boxed<CtxCtx>, o: JoinOrd) -> CtxCtx {
        CtxCtx::JoinR(c.boxed(), cc.boxed(), o)
    }
}

impl CtxCtx {
    pub fn fill(&self, c: Ctx) -> Ctx {
        match self {
            CtxCtx::Hole => c,
            CtxCtx::JoinL(cc1, c2, o) => Ctx::Join(Box::new(cc1.fill(c)), c2.clone(), o.clone()),
            CtxCtx::JoinR(c1, cc2, o) => Ctx::Join(c1.clone(), Box::new(cc2.fill(c)), o.clone()),
        }
    }
    pub fn is_left(&self) -> bool {
        match self {
            CtxCtx::Hole => true,
            CtxCtx::JoinL(cc1, _c2, _o) => cc1.is_left(),
            CtxCtx::JoinR(c1, cc2, o) => cc2.is_left() && (*o == JoinOrd::Unordered || c1.is_unr()),
        }
    }

    pub fn is_right(&self) -> bool {
        match self {
            CtxCtx::Hole => true,
            CtxCtx::JoinL(cc1, c2, o) => {
                cc1.is_right() && (*o == JoinOrd::Unordered || c2.is_unr())
            }
            CtxCtx::JoinR(_c1, cc2, _o) => cc2.is_right(),
        }
    }

    fn pull_left_(&self) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let c2 = cc.pull_left()?;
                Some(CtxS::Join(c2, c, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let c2 = cc.pull_left()?;
                Some(CtxS::Join(c2, c, *o))
            }
        }
    }

    pub fn pull_left(&self) -> Option<Ctx> {
        if self.is_left() {
            self.pull_left_()
        } else {
            None
        }
    }

    fn pull_right_(&self) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let c2 = cc.pull_right()?;
                Some(CtxS::Join(c, c2, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let c2 = cc.pull_right()?;
                Some(CtxS::Join(c, c2, *o))
            }
        }
    }

    pub fn pull_right(&self) -> Option<Ctx> {
        if self.is_right() {
            self.pull_right_()
        } else {
            None
        }
    }

    fn pull_par_(&self) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, _o) => {
                let c2 = cc.pull_par()?;
                Some(CtxS::Join(c, c2, JoinOrd::Unordered))
            }
            CtxCtx::JoinR(c, cc, _o) => {
                let c2 = cc.pull_par()?;
                Some(CtxS::Join(c, c2, JoinOrd::Unordered))
            }
        }
    }

    pub fn pull_par(&self) -> Option<Ctx> {
        if self.is_left() && self.is_right() {
            self.pull_par_()
        } else {
            None
        }
    }

    pub fn pull_closed(&self) -> (Ctx, Ctx) {
        match self {
            CtxCtx::Hole => (Ctx::Empty, Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let (c1, c2) = cc.pull_closed();
                (c1, CtxS::Join(c2, c, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let (c1, c2) = cc.pull_closed();
                (CtxS::Join(c, c1, *o), c2)
            }
        }
    }

    pub fn simplify(&self) -> Self {
        match self {
            CtxCtx::Hole => CtxCtx::Hole,
            CtxCtx::JoinL(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (c1, Ctx::Empty) => c1,
                (c1, c2) => CtxCtxS::JoinL(c1, c2, *o),
            },
            CtxCtx::JoinR(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (Ctx::Empty, c2) => c2,
                (c1, c2) => CtxCtxS::JoinR(c1, c2, *o),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCtx {
    pub ord: Graph<(Id, Type)>,
    pub unr: HashSet<(Id, Type)>,
}

impl SemCtx {
    pub fn empty() -> Self {
        Self {
            ord: Graph::empty(),
            unr: HashSet::new(),
        }
    }
    pub fn bind(x: Id, t: Type) -> Self {
        let mut c = Self::empty();
        if t.is_unr() {
            c.unr.insert((x, t));
        } else {
            c.ord = Graph::singleton((x, t));
        }
        c
    }
    pub fn join(&self, other: &Self, o: JoinOrd) -> Self {
        match o {
            JoinOrd::Ordered => self.plus(other),
            JoinOrd::Unordered => self.union(other),
        }
    }
    pub fn union(&self, other: &Self) -> Self {
        Self {
            ord: self.ord.union(&other.ord),
            unr: self.unr.union(&other.unr).cloned().collect(),
        }
    }
    pub fn plus(&self, other: &Self) -> Self {
        Self {
            ord: self.ord.plus(&other.ord),
            unr: self.unr.union(&other.unr).cloned().collect(),
        }
    }
    pub fn is_subctx_of(&self, other: &Self) -> bool {
        self.ord.is_subgraph_of(&other.ord) && other.unr.is_subset(&self.unr)
    }
}

impl Pretty<()> for Ctx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        match self {
            Ctx::Empty => p.pp("·"),
            Ctx::Bind(x, t) => {
                p.pp(x);
                p.pp(" : ");
                p.pp(t);
            }
            Ctx::Join(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
        }
    }
}

impl Pretty<()> for CtxCtx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        match self {
            CtxCtx::Hole => p.pp("■"),
            CtxCtx::JoinL(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
            CtxCtx::JoinR(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
        }
    }
}

impl<T: Ord + Eq + Hash + Pretty<()>> Pretty<()> for HashSet<T> {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        let mut xs: Vec<_> = self.iter().collect();
        xs.sort();
        p.pp("{");
        for (i, x) in xs.into_iter().enumerate() {
            if i != 0 {
                p.pp(", ");
            }
            p.pp(x);
        }
        p.pp("}");
    }
}

pub struct CtxEnum {
    pub vars: Vec<Id>,
    pub catalanian: Vec<usize>,
    pub cur: usize,
}

pub fn catalanians_up_to(n: usize) -> Vec<usize> {
    let mut catalanian = vec![0, 1];
    for i in 2..=n {
        let mut c = 0;
        for j in 1..i {
            c += catalanian[j] * catalanian[i - j] * 2;
        }
        catalanian.push(c)
    }

    catalanian
}

pub fn gen_ctx(cats: &[usize], vars: &[Id], i: usize) -> Option<Ctx> {
    // eprintln!("gen_ctx({cats:?}, {}, {})", vars.len(), i);
    let mut cur = 0;
    let mut prev = 0;
    let n = vars.len();
    if vars.len() == 0 {
        return None;
    } else if vars.len() == 1 {
        // return Some(Ctx::Bind(fake_span(vars[0].clone()), fake_span(Type::Unit)));
        return Some(Ctx::Bind(
            fake_span(vars[0].clone()),
            fake_span(Type::Chan(fake_span(Session::Owned(fake_span(
                SessionO::End(SessionOp::Send),
            ))))),
        ));
    }
    for x in 1..n {
        cur += cats[x] * cats[n - x] * 2;
        // eprintln!(
        //     "cur = cats[{x}] * cats[{}] = {} * {} = {}",
        //     n - x,
        //     cats[x],
        //     cats[n - x],
        //     cur
        // );
        // eprintln!("Loop {x}, cur {cur}, prev {prev}");
        if i < cur {
            let ord = (i - prev) / (cats[x] * cats[n - x]);
            let i = (i - prev) % (cats[x] * cats[n - x]);
            let j = i % cats[x];
            let k = i / cats[x];
            return Some(Join(
                gen_ctx(cats, &vars[0..x], j)?,
                gen_ctx(cats, &vars[x..n], k)?,
                if ord == 0 { Ordered } else { Unordered },
            ));
        }
        prev = cur;
    }
    // eprintln!("NOT CAUGHT BY LOOP");
    None
}

impl CtxEnum {
    pub fn new(vars: Vec<Id>) -> Self {
        Self {
            catalanian: catalanians_up_to(vars.len()),
            vars,
            cur: 0,
        }
    }
}

impl Iterator for CtxEnum {
    type Item = Ctx;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.catalanian[self.vars.len()] {
            self.cur += 1;
            // eprintln!("\nGenerating {}", self.cur - 1);
            Some(gen_ctx(&self.catalanian, &self.vars, self.cur - 1).unwrap())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::{pretty::pretty_def, sub_set_iter::SubSetIter};

    use super::*;

    fn bind(x: &str) -> Ctx {
        Bind(fake_span(x.to_string()), fake_span(Type::Unit))
    }

    fn u(c1: impl Boxed<Ctx>, c2: impl Boxed<Ctx>) -> Ctx {
        Join(c1, c2, Unordered)
    }
    fn o(c1: impl Boxed<Ctx>, c2: impl Boxed<Ctx>) -> Ctx {
        Join(c1, c2, Ordered)
    }

    fn test_split<S: AsRef<str>>(c: &Ctx, xs: impl IntoIterator<Item = S>) {
        let xs: HashSet<Id> = xs.into_iter().map(|x| x.as_ref().to_string()).collect();
        eprintln!("\n––––––––––––––––––––––––––––––––––––––––––––––––––");
        eprintln!("Ctx:          {}", pretty_def(&c));
        eprintln!("Vars:         {}", pretty_def(&xs));
        let splittable = c.is_splittable(&xs);
        eprintln!("Splittable:   {}", splittable);
        if !splittable {
            return;
        }
        match c.split(&xs) {
            Some((cc, c2)) => {
                let cc = cc.simplify();
                let c2 = c2.simplify();
                eprintln!("Split CtxCtx: {}", pretty_def(&cc));
                eprintln!("Split Ctx:    {}", pretty_def(&c2));

                let cc_vars = cc.fill(Ctx::Empty).lin_vars();
                assert!(
                    cc_vars.is_disjoint(&xs),
                    "Split CtxCtx is not disjoint to xs"
                );

                let c2_vars = c2.vars();
                assert!(c2_vars.is_subset(&xs), "Split Ctx is not a subset of xs");

                let c_res = cc.fill(c2);
                eprintln!("Rejoined Ctx: {}", pretty_def(&c_res));
                assert!(
                    c.to_sem().is_subctx_of(&c_res.to_sem()),
                    "Split context is not super-context of original"
                );

                if c.to_sem() == c_res.to_sem() {
                    eprintln!("Split context is exactly equal to original")
                } else {
                    eprintln!("Split context is worse than original")
                }
            }
            None => assert!(false, "Failed splitting"),
        }
    }

    // #[test]
    // fn split_1() {
    //     let c = o(bind("a"), bind("b"));
    //     test_split(&c, ["a"]);
    //     test_split(&c, ["b"]);
    //     test_split(&c, ["a", "b"]);
    //     test_split::<String>(&c, []);
    // }

    // #[test]
    // fn split_2() {
    //     let c = u(o(bind("a"), bind("b")), o(bind("c"), bind("d")));
    //     test_split(&c, ["a"]);
    //     test_split(&c, ["b"]);
    //     test_split(&c, ["a", "b"]);
    //     test_split::<String>(&c, []);
    // }

    #[test]
    fn split_3() {
        let c = o(bind("a"), o(bind("b"), bind("c")));
        test_split(&c, ["a", "c"]);
    }

    #[test]
    fn ctx_split() {
        let xs = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
            // "f".to_string(),
            // "g".to_string(),
        ];
        let xs_set: HashSet<Id> = xs.iter().cloned().collect();
        let it = CtxEnum::new(xs.clone());
        eprintln!("");
        let mut count = 0;
        for (i, c) in it.enumerate() {
            for (j, ys) in SubSetIter::from(xs_set.clone()).enumerate() {
                eprintln!("\nTest {count}, Ctx {i}, Subset {j}");
                test_split(&c, &ys);
                count += 1;
            }
        }
    }

    // #[test]
    // fn gen_subsets() {
    //     let xs = HashSet::from(["x", "y", "z", "w"]);
    //     let it = SubSetIter::from(xs);
    //     eprintln!("");
    //     for (i, ys) in it.enumerate() {
    //         eprintln!("\nSubset {i} {ys:?}");
    //     }
    // }

    // #[test]
    // fn gen_ctxs() {
    //     let it = CtxEnum::new(vec![
    //         "x".to_string(),
    //         "y".to_string(),
    //         "z".to_string(),
    //         "w".to_string(),
    //         "a".to_string(),
    //     ]);
    //     eprintln!("");
    //     for (i, c) in it.enumerate() {
    //         eprintln!("{}\t{}", i, pretty_def(&c))
    //     }
    // }
}
