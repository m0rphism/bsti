use crate::util::span::{fake_span, Spanned};
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub type Id = String;
pub type SId = Spanned<Id>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mult {
    Unr,
    Lin,
    OrdR,
    OrdL,
}
pub type SMult = Spanned<Mult>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Eff {
    Yes,
    No,
}
pub type SEff = Spanned<Eff>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SessionOp {
    Send,
    Recv,
}
pub type SSessionOp = Spanned<SessionOp>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Session {
    Var(SId),
    Mu(SId, Box<SSession>),
    Op(SessionOp, Box<SType>, Box<SSession>),
    Choice(SessionOp, Vec<(SLabel, SSession)>),
    End(SessionOp),
    Return,
}
pub type SSession = Spanned<Session>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Chan(SSession),
    Arr(SMult, SEff, Box<SType>, Box<SType>),
    Prod(SMult, Box<SType>, Box<SType>),
    Variant(Vec<(SLabel, SType)>),
    Unit,
    Int,
    Bool,
    String,
}
pub type SType = Spanned<Type>;

pub type Label = String;
pub type SLabel = Spanned<Label>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    Var(SId),
    Pair(Box<SPattern>, Box<SPattern>),
    //Inj(Label, Box<SPattern>),
}
pub type SPattern = Spanned<Pattern>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    pub id: SId,
    pub pats: Vec<SPattern>,
    pub body: SExpr,
}
pub type SClause = Spanned<Clause>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Const {
    Unit,
    Int(i64),
    Bool(bool),
    String(String),
}

impl Const {
    pub fn type_(&self) -> Type {
        match self {
            Const::Unit => Type::Unit,
            Const::Int(_) => Type::Int,
            Const::Bool(_) => Type::Bool,
            Const::String(_) => Type::String,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op1 {
    Neg,
    Not,
    ToStr,
    Print,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op2 {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(SId),
    Abs(SId, Box<SExpr>),
    App(Box<SExpr>, Box<SExpr>),
    AppL(Box<SExpr>, Box<SExpr>),
    Borrow(SId),

    Let(SId, Box<SExpr>, Box<SExpr>),

    Pair(Box<SExpr>, Box<SExpr>),
    LetPair(SId, SId, Box<SExpr>, Box<SExpr>),

    Inj(SLabel, Box<SExpr>),
    CaseSum(Box<SExpr>, Vec<(SLabel, SId, SExpr)>),
    If(Box<SExpr>, Box<SExpr>, Box<SExpr>),

    Fork(Box<SExpr>),
    New(SSession),
    Send(Box<SExpr>, Box<SExpr>),
    Recv(Box<SExpr>),
    Select(SLabel, Box<SExpr>),
    Offer(Box<SExpr>),
    Drop(Box<SExpr>),
    End(SessionOp, Box<SExpr>),
    Const(Const),

    Ann(Box<SExpr>, SType),

    LetDecl(SId, SType, Vec<SClause>, Box<SExpr>),
    Seq(Box<SExpr>, Box<SExpr>),
    Op1(Op1, Box<SExpr>),
    Op2(Op2, Box<SExpr>, Box<SExpr>),
}
pub type SExpr = Spanned<Expr>;

pub fn without<T: Hash + Eq>(mut xs: HashSet<T>, x: &T) -> HashSet<T> {
    xs.remove(x);
    xs
}

pub fn union<T: Hash + Eq>(mut xs: HashSet<T>, ys: HashSet<T>) -> HashSet<T> {
    for y in ys {
        xs.insert(y);
    }
    xs
}

impl SessionOp {
    pub fn dual(self) -> Self {
        match self {
            SessionOp::Send => SessionOp::Recv,
            SessionOp::Recv => SessionOp::Send,
        }
    }
}

fn merge_clauses<T: Clone>(
    cs1: &[(SLabel, T)],
    cs2: &[(SLabel, T)],
    sub: bool,
) -> Option<Vec<(SLabel, T, T)>> {
    let mut out = vec![];
    for (l2, s2) in cs2 {
        if let Some((_, s1)) = cs1.iter().find(|(l1, _)| l2 == l1) {
            out.push((l2.clone(), s1.clone(), s2.clone()))
        } else {
            return None;
        }
    }
    if !sub {
        for (l1, _) in cs1 {
            if let None = cs2.iter().find(|(l2, _)| l1 == l2) {
                return None;
            }
        }
    }
    Some(out)
}

impl Session {
    fn subst(&self, x: &Id, s_new: &Self) -> Self {
        match self {
            Session::Var(y) if *x == **y => s_new.clone(),
            Session::Var(y) => Session::Var(y.clone()),
            Session::Mu(y, e) => Session::Mu(y.clone(), Box::new(fake_span(e.subst(x, s_new)))),
            Session::Op(op, t, s) => Session::Op(
                op.clone(),
                t.clone(),
                Box::new(fake_span(s.subst(x, s_new))),
            ),
            Session::Choice(op, cs) => {
                let cs2 = cs
                    .iter()
                    .map(|(l, s)| (l.clone(), fake_span(s.subst(x, s_new))))
                    .collect();
                Session::Choice(op.clone(), cs2)
            }
            Session::End(op) => Session::End(op.clone()),
            Session::Return => Session::Return,
        }
    }
    fn unfold(&self, x: &SId) -> Self {
        self.subst(
            x,
            &Session::Mu(x.clone(), Box::new(fake_span(self.clone()))),
        )
    }
    pub fn unfold_if_mu(&self) -> Self {
        match self {
            Session::Mu(x, s) => s.unfold(x).unfold_if_mu(),
            _ => self.clone(),
        }
    }
    fn sem_eq_(&self, other: &Self, seen: &HashSet<(Session, Session)>) -> bool {
        let mut seen = seen.clone();
        if !seen.insert((self.clone(), other.clone())) {
            return true;
        } else {
            match (self, other) {
                (Session::Op(op1, t1, s1), Session::Op(op2, t2, s2)) => {
                    op1 == op2 && t1.sem_eq(t2) && s1.sem_eq_(s2, &seen)
                }
                (Session::End(op1), Session::End(op2)) => op1 == op2,
                (Session::Return, Session::Return) => true,
                (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) if op1 == op2 => {
                    if let Some(cs) = merge_clauses(&cs1, &cs2, false) {
                        cs.iter().all(|(_, s1, s2)| s1.sem_eq_(s2, &seen))
                    } else {
                        false
                    }
                }
                (Session::Mu(x1, s1), _) => s1.unfold(&x1).sem_eq_(other, &seen),
                (_, Session::Mu(x2, s2)) => self.sem_eq_(&s2.unfold(&x2), &seen),
                (Session::Var(_x1), _) => unreachable!(),
                (_, Session::Var(_x2)) => unreachable!(),
                _ => false,
            }
        }
    }
    pub fn sem_eq(&self, other: &Self) -> bool {
        self.sem_eq_(other, &HashSet::new())
    }
    fn split_(&self, p: &Session, seen: &HashSet<(Session, Session)>) -> Result<Option<Self>, ()> {
        let mut seen = seen.clone();
        if !seen.insert((self.clone(), p.clone())) {
            Ok(None)
        } else {
            match (self, p) {
                (_, Session::End(_op2)) => Err(()),
                (_, Session::Return) => Ok(Some(self.clone())),
                (Session::Op(op1, t1, s1), Session::Op(op2, t2, s2))
                    if op1 == op2 && t1.sem_eq(t2) =>
                {
                    s1.split_(s2, &seen)
                }
                (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) if op1 == op2 => {
                    if let Some(cs) = merge_clauses(&cs1, &cs2, *op1 == SessionOp::Send) {
                        let cs = cs
                            .iter()
                            .map(|(_, s1, s2)| s1.split_(s2, &seen))
                            .collect::<Result<Vec<_>, ()>>()?;
                        let mut it = cs.into_iter().flatten();
                        if let Some(r) = it.next() {
                            if it.all(|r2| r.sem_eq(&r2)) {
                                Ok(Some(r))
                            } else {
                                Err(())
                            }
                        } else {
                            Ok(None)
                        }
                    } else {
                        return Err(());
                    }
                }
                (Session::Mu(x1, s1), _) => s1.unfold(&x1).split_(p, &seen),
                (_, Session::Mu(x2, s2)) => self.split_(&s2.unfold(&x2), &seen),
                (Session::Var(_x1), _) => unreachable!(),
                (_, Session::Var(_x2)) => unreachable!(),
                _ => Err(()),
            }
        }
    }
    pub fn split(&self, s1: &Session) -> Option<Self> {
        let r = self.split_(s1, &HashSet::new()).ok()?;
        r
    }
    pub fn dual(&self) -> Self {
        match self {
            Session::Op(op, t, s) => {
                Session::Op(op.dual(), t.clone(), Box::new(fake_span(s.dual())))
            }
            Session::Choice(op, cs) => {
                let cs2: Vec<(SLabel, SSession)> = cs
                    .iter()
                    .map(|(l, s)| (l.clone(), fake_span(s.dual())))
                    .collect();
                Session::Choice(op.dual(), cs2)
            }
            Session::End(op) => Session::End(op.dual()),
            Session::Return => Session::Return,
            Session::Mu(x, s) => Session::Mu(x.clone(), Box::new(fake_span(s.dual()))),
            Session::Var(x) => Session::Var(x.clone()),
        }
    }

    pub fn join(&self, s: &Session) -> Session {
        match self {
            Session::Op(o, t, s1) => {
                Session::Op(o.clone(), t.clone(), Box::new(fake_span(s1.join(s))))
            }
            Session::Choice(op, cs) => {
                let cs2: Vec<(SLabel, SSession)> = cs
                    .iter()
                    .map(|(l, s1)| (l.clone(), fake_span(s1.join(s))))
                    .collect();
                Session::Choice(*op, cs2)
            }
            Session::Return | Session::End(_) => s.clone(),
            Session::Mu(x, s1) => Session::Mu(x.clone(), Box::new(fake_span(s1.join(s)))),
            Session::Var(x) => Session::Var(x.clone()),
        }
    }

    pub fn is_owned(&self) -> bool {
        match self {
            Session::Var(_x) => true,
            Session::Mu(_x, s) => s.is_owned(),
            Session::Op(_op, _t, s) => s.is_owned(),
            Session::Choice(_op, cs) => cs.iter().all(|(_l, s)| s.is_owned()),
            Session::End(_op) => true,
            Session::Return => false,
        }
    }

    pub fn is_borrowed(&self) -> bool {
        !self.is_owned()
    }
}

#[derive(Debug, Clone)]
pub struct TypeSemEq(pub Type);

impl PartialEq for TypeSemEq {
    fn eq(&self, other: &Self) -> bool {
        self.0.sem_eq(&other.0)
    }
}

impl Eq for TypeSemEq {}

// Safe, but not performant
impl Hash for TypeSemEq {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Expr {
    pub fn free_vars(&self) -> HashSet<Id> {
        match self {
            Expr::Const(_) => HashSet::new(),
            Expr::New(_r) => HashSet::new(),
            Expr::Drop(e) => e.free_vars(),
            Expr::Var(x) => HashSet::from([x.val.clone()]),
            Expr::Abs(x, e) => without(e.free_vars(), &x.val),
            Expr::App(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Pair(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::LetPair(x, y, e1, e2) => {
                union(e1.free_vars(), without(without(e2.free_vars(), y), x))
            }
            Expr::Ann(e, _t) => e.free_vars(),
            Expr::Let(x, e1, e2) => union(e1.free_vars(), without(e2.free_vars(), x)),
            Expr::Seq(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::LetDecl(_x, _t, cs, e) => {
                let mut xs = HashSet::new();
                for c in cs {
                    xs.extend(c.free_vars())
                }
                union(xs, e.free_vars())
            }
            Expr::AppL(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Borrow(x) => HashSet::from([x.val.clone()]),
            Expr::Inj(_l, e) => e.free_vars(),
            Expr::CaseSum(e, cs) => {
                let mut xs = e.free_vars();
                for (_l, x, e) in cs {
                    xs = union(xs, without(e.free_vars(), &x.val));
                }
                xs
            }
            Expr::Fork(e) => e.free_vars(),
            Expr::Send(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Recv(e) => e.free_vars(),
            Expr::End(_l, e) => e.free_vars(),
            Expr::Op1(_op1, e) => e.free_vars(),
            Expr::Op2(_op2, e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::If(e, e1, e2) => union(e.free_vars(), union(e1.free_vars(), e2.free_vars())),
            Expr::Select(_l, e) => e.free_vars(),
            Expr::Offer(e) => e.free_vars(),
        }
    }
}

impl Clause {
    pub fn free_vars(&self) -> HashSet<Id> {
        let mut vars = self.body.free_vars();
        for p in &self.pats {
            vars = vars.difference(&p.bound_vars()).cloned().collect();
        }
        vars
    }
}

impl Pattern {
    pub fn bound_vars(&self) -> HashSet<Id> {
        match self {
            Pattern::Var(x) => HashSet::from([x.val.clone()]),
            Pattern::Pair(p1, p2) => union(p1.bound_vars(), p2.bound_vars()),
            //Pattern::Inj(_l, p) => p.bound_vars(),
        }
    }
}

//impl Eq for Session {}
//
//// Inefficient but correct for the custom equality
//impl Hash for Session {
//    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
//}

impl Type {
    pub fn sem_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Chan(s1), Type::Chan(s2)) => s1.sem_eq(s2),
            (Type::Arr(m1, p1, t11, t12), Type::Arr(m2, p2, t21, t22)) => {
                m1 == m2 && p1 == p2 && t11.sem_eq(t21) && t12.sem_eq(t22)
            }
            (Type::Prod(m1, t11, t12), Type::Prod(m2, t21, t22)) => {
                m1 == m2 && t11.sem_eq(t21) && t12.sem_eq(t22)
            }
            (Type::Variant(cs1), Type::Variant(cs2)) => {
                if let Some(cs) = merge_clauses(&cs1, &cs2, false) {
                    cs.iter().all(|(_, t1, t2)| t1.sem_eq(t2))
                } else {
                    false
                }
            }
            (Type::Unit, Type::Unit) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            _ => false,
        }
    }
    pub fn is_unr(&self) -> bool {
        match self {
            Type::Chan(_) => false,
            Type::Arr(m, _, _, _) => m.val == Mult::Unr,
            Type::Prod(m, t1, t2) => m.val == Mult::Unr || (t1.is_unr() && t2.is_unr()),
            Type::Variant(cs) => cs.iter().all(|(_, t)| t.is_unr()),
            Type::Unit => true,
            Type::Int => true,
            Type::Bool => true,
            Type::String => true,
        }
    }

    pub fn is_ord(&self) -> bool {
        !self.is_unr()
    }
}

impl Eff {
    pub fn lub(p1: Eff, p2: Eff) -> Eff {
        match p1 {
            Eff::Yes => Eff::Yes,
            Eff::No => p2,
        }
    }

    pub fn leq(e1: Eff, e2: Eff) -> bool {
        match (e1, e2) {
            (Eff::Yes, Eff::Yes) => true,
            (Eff::Yes, Eff::No) => false,
            (Eff::No, _) => true,
        }
    }
}
