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

#[derive(Debug, Clone)]
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
    AppR(Box<SExpr>, Box<SExpr>),
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

impl Session {
    pub fn split(&self, s1: &Session) -> Option<Self> {
        match (self, s1) {
            (_, Session::Return) => Some(self.clone()),
            (Session::Op(op1, t1, s1), Session::Op(op2, t2, s2)) if op1 == op2 && t1.eq(&t2) => {
                s1.split(&s2)
            }
            _ => None,
        }
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
            Session::Return | Session::End(_) => s.clone(), // TODO
            Session::Mu(x, s) => todo!(),
            Session::Var(x) => todo!(),
        }
    }

    pub fn is_owned(&self) -> bool {
        !self.is_borrowed()
    }

    pub fn is_borrowed(&self) -> bool {
        match self {
            Session::Var(x) => todo!(), // TODO
            Session::Mu(x, s) => s.is_borrowed(),
            Session::Op(op, t, s) => s.is_borrowed(),
            Session::Choice(s, cs) => cs.first().unwrap().1.is_borrowed(), // TODO
            Session::End(op) => false,
            Session::Return => true,
        }
    }
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

impl PartialEq for Session {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Session::Op(op1, t1, s1), Session::Op(op2, t2, s2)) => {
                op1 == op2 && t1.eq(t2) && s1.eq(s2)
            }
            (Session::End(op1), Session::End(op2)) => op1 == op2,
            (Session::Return, Session::Return) => true,
            (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) => {
                todo!()
            }
            (Session::Mu(x1, s1), Session::Mu(x2, s2)) => todo!(),
            (Session::Var(x1), Session::Var(x2)) => todo!(),
            _ => false,
        }
    }
}

impl Eq for Session {}

// Inefficient but correct for the custom equality
impl Hash for Session {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Type {
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
