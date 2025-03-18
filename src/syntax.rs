use crate::{regex, util::span::Spanned};
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Unit,
    Regex(SRegex),
    Arr(SMult, SEff, Box<SType>, Box<SType>),
    Prod(SMult, Box<SType>, Box<SType>),
}
pub type SType = Spanned<Type>;

pub type Regex = regex::Regex<u8>;
pub type SRegex = Spanned<Regex>;

pub type Word = String;
pub type SWord = Spanned<Word>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    Var(SId),
    Pair(Box<SPattern>, Box<SPattern>),
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
    Unit,
    New(SRegex),
    Write(SRegex, Box<SExpr>),
    Split(SRegex, Box<SExpr>),
    Drop(Box<SExpr>),
    Loc(SLoc),
    Var(SId),
    Abs(Option<SMult>, SId, Box<SExpr>),
    App(Option<Mult>, Box<SExpr>, Box<SExpr>),
    AppBorrow(Box<SExpr>, SId),
    Pair(Option<SMult>, Box<SExpr>, Box<SExpr>),
    LetPair(SId, SId, Box<SExpr>, Box<SExpr>),
    LetDecl(SId, SType, Vec<SClause>, Box<SExpr>),
    Let(SId, Box<SExpr>, Box<SExpr>),
    Seq(Box<SExpr>, Box<SExpr>),
    Ann(Box<SExpr>, SType),
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

impl Expr {
    pub fn free_vars(&self) -> HashSet<Id> {
        match self {
            Expr::Unit => HashSet::new(),
            Expr::New(_r) => HashSet::new(),
            Expr::Write(_w, e) => e.free_vars(),
            Expr::Split(_r, e) => e.free_vars(),
            Expr::Drop(e) => e.free_vars(),
            Expr::Loc(_l) => HashSet::new(),
            Expr::Var(x) => HashSet::from([x.val.clone()]),
            Expr::Abs(_m, x, e) => without(e.free_vars(), &x.val),
            Expr::App(_om, e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::AppBorrow(e, x) => union(e.free_vars(), HashSet::from([x.val.clone()])),
            Expr::Pair(_m, e1, e2) => union(e1.free_vars(), e2.free_vars()),
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
        }
    }
}

impl Type {
    pub fn is_subtype_of(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Unit, Type::Unit) => true,
            (Type::Regex(r1), Type::Regex(r2)) => r1.is_subseteq_of(r2),
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
            (Type::Regex(r1), Type::Regex(r2)) => r1.is_equal_to(r2),
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
            Type::Regex(_) => false,
            Type::Arr(m, _, _, _) => m.val == Mult::Unr,
            Type::Prod(m, _, _) => m.val == Mult::Unr,
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
