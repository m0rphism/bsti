use crate::{
    regex,
    util::span::{fake_span, Spanned},
};
use std::{collections::HashSet, hash::Hash};

pub type Id = String;
pub type SId = Spanned<Id>;

pub type Loc = usize;
pub type SLoc = Spanned<Loc>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mult {
    Unr,
    Lin,
    OrdL,
    OrdR,
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
pub enum SessionO {
    Op(SessionOp, Box<SType>, Box<SSessionO>),
    End(SessionOp),
}
pub type SSessionO = Spanned<SessionO>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SessionB {
    Op(SessionOp, Box<SType>, Box<SSessionB>),
    Return,
}
pub type SSessionB = Spanned<SessionB>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Session {
    Owned(SSessionO),
    Borrowed(SSessionB),
}
pub type SSession = Spanned<Session>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Unit,
    Chan(SSession),
    Arr(SMult, SEff, Box<SType>, Box<SType>),
    Prod(SMult, Box<SType>, Box<SType>),
    Variant(Vec<(SSumLabel, SType)>),
}
pub type SType = Spanned<Type>;

pub type SumLabel = String;
pub type SSumLabel = Spanned<SumLabel>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    Var(SId),
    Pair(Box<SPattern>, Box<SPattern>),
    Inj(SumLabel, Box<SPattern>),
}
pub type SPattern = Spanned<Pattern>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    pub id: SId,
    pub pats: Vec<SPattern>,
    pub body: SExpr,
}
pub type SClause = Spanned<Clause>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(SId),
    Abs(SId, Box<SExpr>),
    App(Box<SExpr>, Box<SExpr>),
    AppR(Box<SExpr>, Box<SExpr>),
    Borrow(SId),

    Let(SId, Box<SExpr>, Box<SExpr>),

    Pair(Box<SExpr>, Box<SExpr>),
    LetPair(SId, SId, Box<SExpr>, Box<SExpr>),

    Inj(SSumLabel, Box<SExpr>),
    CaseSum(Box<SExpr>, Vec<(SSumLabel, SId, SExpr)>),

    Fork(Box<SExpr>),
    New(SSessionO),
    Send(Box<SExpr>, Box<SExpr>),
    Recv(Box<SExpr>),
    Drop(Box<SExpr>),
    End(SessionOp, Box<SExpr>),
    Unit,

    Ann(Box<SExpr>, SType),

    LetDecl(SId, SType, Vec<SClause>, Box<SExpr>),
    Seq(Box<SExpr>, Box<SExpr>),
    // Int(i64),
    // Float(f64),
    // String(String),
    // Bool(bool),
    // List(Vec<Expr>),
    // None,
    // ListAccess(Box<Expr>, Box<Expr>),
    // Binop(Binop, Box<Expr>, Box<Expr>),
    // Unop(Unop, Box<Expr>),
    // Scope(Program),
    // Loc(Loc),
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

impl SessionO {
    pub fn split(&self, s1: &SessionB) -> Option<Self> {
        match (self, s1) {
            (_, SessionB::Return) => Some(self.clone()),
            (SessionO::Op(op1, t1, s1), SessionB::Op(op2, t2, s2))
                if op1 == op2 && t1.is_equal_to(&t2) =>
            {
                s1.split(&s2)
            }
            _ => None,
        }
    }
}

impl SessionB {
    pub fn split(&self, s1: &SessionB) -> Option<Self> {
        match (self, s1) {
            (_, SessionB::Return) => Some(self.clone()),
            (SessionB::Op(op1, t1, s1), SessionB::Op(op2, t2, s2))
                if op1 == op2 && t1.is_equal_to(&t2) =>
            {
                s1.split(&s2)
            }
            _ => None,
        }
    }

    pub fn join_owned(&self, s: &SessionO) -> SessionO {
        match self {
            SessionB::Op(o, t, s1) => {
                SessionO::Op(o.clone(), t.clone(), Box::new(fake_span(s1.join_owned(s))))
            }
            SessionB::Return => s.clone(),
        }
    }

    pub fn join_borrowed(&self, s: &SessionB) -> SessionB {
        match self {
            SessionB::Op(o, t, s1) => SessionB::Op(
                o.clone(),
                t.clone(),
                Box::new(fake_span(s1.join_borrowed(s))),
            ),
            SessionB::Return => s.clone(),
        }
    }

    pub fn join(&self, s: &Session) -> Session {
        match s {
            Session::Owned(s) => Session::Owned(fake_span(self.join_owned(s))),
            Session::Borrowed(s) => Session::Borrowed(fake_span(self.join_borrowed(s))),
        }
    }
}

impl Session {
    pub fn split(&self, s1: &SessionB) -> Option<Self> {
        match self {
            Session::Owned(s) => s.split(s1).map(|s2| Session::Owned(fake_span(s2))),
            Session::Borrowed(s) => s.split(s1).map(|s2| Session::Borrowed(fake_span(s2))),
        }
    }
    pub fn join(&self, s2: &Session) -> Session {
        match self {
            Session::Owned(s1) => Session::Owned(s1.clone()), // TODO: this should be okay
            Session::Borrowed(s1) => s1.join(s2),
        }
    }
}

impl Expr {
    pub fn free_vars(&self) -> HashSet<Id> {
        match self {
            Expr::Unit => HashSet::new(),
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
            Expr::AppR(e1, e2) => union(e1.free_vars(), e2.free_vars()),
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
            Pattern::Inj(_l, p) => p.bound_vars(),
        }
    }
}

impl SessionO {
    //pub fn is_subtype_of(&self, other: &Self) -> bool {
    //    match (other, self) {
    //        (SessionO::Op(o1, t1, s1), SessionO::Op(o2, t2, s2)) => todo!(),
    //        (SessionO::Op(o1, t1, s1), SessionO::End(o2)) => todo!(),
    //        (SessionO::End(o1), SessionO::Op(o2, t2, s2)) => todo!(),
    //        (SessionO::End(o1), SessionO::End(o2)) => todo!(),
    //    }
    //}
    pub fn is_equal_to(&self, other: &Self) -> bool {
        match (self, other) {
            (SessionO::Op(op1, t1, s1), SessionO::Op(op2, t2, s2)) => {
                op1 == op2 && t1.is_equal_to(t2) && s1.is_equal_to(s2)
            }
            (SessionO::Op(_, _, _), SessionO::End(_)) => false,
            (SessionO::End(_), SessionO::Op(_, _, _)) => false,
            (SessionO::End(op1), SessionO::End(op2)) => op1 == op2,
        }
    }
}

impl SessionB {
    //pub fn is_subtype_of(&self, other: &Self) -> bool {
    //    match (other, self) {
    //    }
    //}
    pub fn is_equal_to(&self, other: &Self) -> bool {
        match (self, other) {
            (SessionB::Op(op1, t1, s1), SessionB::Op(op2, t2, s2)) => {
                op1 == op2 && t1.is_equal_to(t2) && s1.is_equal_to(s2)
            }
            (SessionB::Op(_, _, _), SessionB::Return) => false,
            (SessionB::Return, SessionB::Op(_, _, _)) => false,
            (SessionB::Return, SessionB::Return) => true,
        }
    }
}

impl Session {
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        unimplemented!()
        //match (self, other) {
        //    (Session::Owned(s1), Session::Owned(s2)) => s1.is_subtype_of(s2),
        //    (Session::Owned(_s1), Session::Borrowed(_s2)) => false,
        //    (Session::Borrowed(_s1), Session::Owned(_s2)) => false,
        //    (Session::Borrowed(s1), Session::Borrowed(s2)) => s1.is_subtype_of(s2),
        //}
    }
    pub fn is_equal_to(&self, other: &Self) -> bool {
        match (self, other) {
            (Session::Owned(s1), Session::Owned(s2)) => s1.is_equal_to(s2),
            (Session::Owned(_s1), Session::Borrowed(_s2)) => false,
            (Session::Borrowed(_s1), Session::Owned(_s2)) => false,
            (Session::Borrowed(s1), Session::Borrowed(s2)) => s1.is_equal_to(s2),
        }
    }
}

impl Type {
    pub fn is_subtype_of(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Unit, Type::Unit) => true,
            (Type::Chan(s1), Type::Chan(s2)) => s1.is_subtype_of(s2),
            (Type::Arr(m1, p1, t11, t12), Type::Arr(m2, p2, t21, t22)) => {
                m1.val == m2.val
                    && p1.val == p2.val
                    && t11.is_subtype_of(t21)
                    && t22.is_subtype_of(t12)
            }
            (Type::Prod(m1, t11, t12), Type::Prod(m2, t21, t22)) => {
                m1.val == m2.val && t11.is_subtype_of(t21) && t12.is_subtype_of(t22)
            }
            (_, _) => false,
        }
    }
    pub fn is_equal_to(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Unit, Type::Unit) => true,
            (Type::Chan(s1), Type::Chan(s2)) => s1.is_equal_to(s2),
            (Type::Arr(m1, p1, t11, t12), Type::Arr(m2, p2, t21, t22)) => {
                m1.val == m2.val && p1.val == p2.val && t11.is_equal_to(t21) && t12.is_equal_to(t22)
            }
            (Type::Prod(m1, t11, t12), Type::Prod(m2, t21, t22)) => {
                m1.val == m2.val && t11.is_equal_to(t21) && t12.is_equal_to(t22)
            }
            (_, _) => false,
        }
    }

    pub fn is_unr(&self) -> bool {
        match self {
            Type::Unit => true,
            Type::Chan(_) => false,
            Type::Arr(m, _, _, _) => m.val == Mult::Unr,
            Type::Prod(m, _, _) => m.val == Mult::Unr,
            Type::Variant(cs) => cs.iter().all(|(_, t)| t.is_unr()),
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

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
// pub enum Binop {
//     Add,
//     Mul,
//     Sub,
//     Div,
//     And,
//     Or,
//     Lt,
//     Le,
//     Gt,
//     Ge,
//     Eq,
//     Neq,
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
// pub enum Unop {
//     Not,
//     Neg,
// }
