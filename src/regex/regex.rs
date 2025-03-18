use std::collections::{HashSet, VecDeque};
use std::fmt::{Debug, Display};
use std::hash::Hash;

// Syntax

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Regex<C> {
    Empty,
    Eps,
    Char(C),
    Or(Box<Regex<C>>, Box<Regex<C>>),
    And(Box<Regex<C>>, Box<Regex<C>>),
    Seq(Box<Regex<C>>, Box<Regex<C>>),
    Star(Box<Regex<C>>),
    Neg(Box<Regex<C>>),
}

// Smart constructors

pub use Regex::Char as char_;
pub use Regex::Empty as empty;
pub use Regex::Eps as eps;

use crate::util::pretty::Pretty;

use super::pretty::Char;
use super::{Example, Realizable};

pub fn or<C>(e1: Regex<C>, e2: Regex<C>) -> Regex<C> {
    Regex::Or(Box::new(e1), Box::new(e2))
}
pub fn and<C>(e1: Regex<C>, e2: Regex<C>) -> Regex<C> {
    Regex::And(Box::new(e1), Box::new(e2))
}
pub fn seq<C>(e1: Regex<C>, e2: Regex<C>) -> Regex<C> {
    Regex::Seq(Box::new(e1), Box::new(e2))
}
pub fn star<C>(e: Regex<C>) -> Regex<C> {
    Regex::Star(Box::new(e))
}
pub fn neg<C>(e: Regex<C>) -> Regex<C> {
    Regex::Neg(Box::new(e))
}

// Display

impl<C: Display> Display for Regex<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Regex::Empty => write!(f, "∅"),
            Regex::Eps => write!(f, "ε"),
            Regex::Char(c) => write!(f, "{c}"),
            Regex::Or(e1, e2) => write!(f, "({e1}|{e2})"),
            Regex::And(e1, e2) => write!(f, "({e1}&{e2})"),
            Regex::Seq(e1, e2) => write!(f, "({e1}{e2})"),
            Regex::Star(e) => write!(f, "({e}*)"),
            Regex::Neg(e) => write!(f, "(~{e})"),
        }
    }
}

impl<C: Copy + Debug + Eq + Hash + Ord> Regex<C> {
    pub fn nullable(&self) -> bool {
        match self {
            Regex::Empty => false,
            Regex::Eps => true,
            Regex::Char(_) => false,
            Regex::Or(e1, e2) => e1.nullable() || e2.nullable(),
            Regex::And(e1, e2) => e1.nullable() && e2.nullable(),
            Regex::Seq(e1, e2) => e1.nullable() && e2.nullable(),
            Regex::Star(_) => true,
            Regex::Neg(e) => !e.nullable(),
        }
    }
    pub fn is_empty(&self) -> bool {
        match self {
            Regex::Empty => true,
            Regex::Eps => false,
            Regex::Char(_) => false,
            Regex::Or(e1, e2) => e1.is_empty() && e2.is_empty(),
            Regex::And(e1, e2) => e1.is_empty() || e2.is_empty(),
            Regex::Seq(e1, e2) => e1.is_empty() || e2.is_empty(),
            Regex::Star(_) => false,
            Regex::Neg(e) => !e.is_empty(),
        }
    }
    pub fn deriv(&self, c: C) -> Self {
        match self {
            Regex::Empty => Regex::Empty,
            Regex::Eps => Regex::Empty,
            Regex::Char(c2) if &c == c2 => Regex::Eps,
            Regex::Char(_) => Regex::Empty,
            Regex::Or(e1, e2) => or(e1.deriv(c), e2.deriv(c)),
            Regex::And(e1, e2) => and(e1.deriv(c), e2.deriv(c)),
            Regex::Seq(e1, e2) if e1.nullable() => {
                or(seq(e1.deriv(c), e2.as_ref().clone()), e2.deriv(c))
            }
            Regex::Seq(e1, e2) => seq(e1.deriv(c), e2.as_ref().clone()),
            Regex::Star(e) => seq(e.deriv(c), star(e.as_ref().clone())),
            Regex::Neg(e) => neg(e.deriv(c)),
        }
    }
    pub fn deriv_word(&self, cs: impl IntoIterator<Item = C>) -> Self {
        let mut r = self.clone();
        for c in cs {
            r = r.deriv(c);
        }
        r
    }
    pub fn accepts(&self, cs: impl IntoIterator<Item = C>) -> bool {
        self.deriv_word(cs).nullable()
    }

    pub fn simplify(&self) -> Regex<C> {
        match self {
            Regex::Empty => empty,
            Regex::Eps => eps,
            Regex::Char(c) => char_(*c),
            Regex::Or(e1, e2) => match (e1.simplify(), e2.simplify()) {
                (Regex::Empty, e2) => e2,
                (e1, Regex::Empty) => e1,
                (e1, e2) => canonical_or(&e1, &e2),
            },
            Regex::And(e1, e2) => match (e1.simplify(), e2.simplify()) {
                (Regex::Neg(e1), e2) if *e1 == empty => e2,
                (e1, Regex::Neg(e2)) if *e2 == empty => e1,
                (Regex::Empty, _e2) => empty,
                (_e1, Regex::Empty) => empty,
                (Regex::Eps, _) => eps,
                (_, Regex::Eps) => eps,
                (e1, e2) => and(e1, e2),
            },
            Regex::Seq(e1, e2) => match (e1.simplify(), e2.simplify()) {
                (Regex::Empty, _e2) => empty,
                (_e1, Regex::Empty) => empty,
                (Regex::Eps, e2) => e2,
                (e1, Regex::Eps) => e1,
                (e1, e2) => seq(e1, e2),
            },
            Regex::Star(e) => match e.simplify() {
                Regex::Empty => eps,
                Regex::Eps => eps,
                Regex::Star(e) => star(e.as_ref().clone()),
                e => star(e),
            },
            Regex::Neg(e) => match e.simplify() {
                Regex::Neg(e) => *e,
                e => neg(e),
            },
        }
    }
}

pub fn canonical_or<C: Copy + Debug + Eq + Hash + Ord>(e1: &Regex<C>, e2: &Regex<C>) -> Regex<C> {
    let mut args = vec![];
    let mut queue = VecDeque::new();
    queue.push_back(e1);
    queue.push_back(e2);
    while let Some(e) = queue.pop_front() {
        match e {
            Regex::Or(e1, e2) => {
                queue.push_back(e1);
                queue.push_back(e2);
            }
            _ => args.push(e),
        }
    }
    args.sort();
    args.dedup();
    let mut it = args.into_iter().rev().cloned();
    let mut e = it.next().unwrap();
    for e2 in it {
        e = or(e2, e);
    }
    e
}

// Product Derivatives as in the paper
// 'Manipulation of Extended Regular Expressions with Derivatives'

impl<C: Copy + Debug + Eq + Hash + Ord> Regex<C> {
    pub fn canonical(&self) -> Regex<C> {
        // eprintln!("–––––––––––––––––––––––");
        // eprintln!("> {self:?}");
        let res = match self {
            Regex::Empty => empty,
            Regex::Eps => eps,
            Regex::Char(c) => seq(char_(*c), eps),
            Regex::Or(e1, e2) => match (e1.canonical(), e2.canonical()) {
                (Regex::Empty, e2) => e2,
                (e1, Regex::Empty) => e1,
                (e1, e2) => seq(or(e1.canonical(), e2.canonical()), eps),
            },
            Regex::And(_e1, _e2) => panic!("Cannot canonicalize regex {self:?}"),
            Regex::Seq(e1, e2) => match (e1.canonical(), e2.canonical()) {
                (Regex::Empty, _e2) => empty,
                (_e1, Regex::Empty) => empty,
                (Regex::Eps, e2) => e2,
                (e1, Regex::Eps) => e1,
                (Regex::Seq(e1, e2), e3) => seq(*e1, seq(*e2, e3).canonical()),
                (e1, e2) => seq(e1, e2),
            },
            Regex::Star(e) => match e.canonical() {
                Regex::Empty => eps,
                e => seq(star(e), eps),
            },
            Regex::Neg(_) => panic!("Cannot canonicalize regex {self:?}"),
        };
        // eprintln!("< {res:?}");
        res
    }
    fn is_canonical_(&self) -> bool {
        match self {
            Regex::Empty => false,
            Regex::Eps => true,
            Regex::Char(_) => false,
            Regex::Or(_, _) => false,
            Regex::And(_, _) => panic!("Cannot check canonicalize regex {self:?}"),
            Regex::Seq(e1, e2) => match e1.as_ref() {
                Regex::Empty => false,
                Regex::Eps => false,
                Regex::Char(_) => e2.is_canonical_(),
                Regex::Or(e11, e12) => {
                    e11.is_canonical_() && e12.is_canonical_() && e2.is_canonical_()
                }
                Regex::And(_, _) => panic!("Cannot check canonicalize regex {self:?}"),
                Regex::Seq(_, _) => false,
                Regex::Star(e11) => e11.is_canonical_() && e2.is_canonical_(),
                Regex::Neg(_) => panic!("Cannot check canonicalize regex {self:?}"),
            },
            Regex::Star(_) => false,
            Regex::Neg(_) => panic!("Cannot check canonicalize regex {self:?}"),
        }
    }
    pub fn is_canonical(&self) -> bool {
        match self {
            Regex::Empty => true,
            _ => self.is_canonical_(),
        }
    }
    pub fn deriv_re(&self, e: &Regex<C>) -> Regex<C> {
        let c = self.canonical();
        assert!(
            c.is_canonical(),
            "{c:?} is not canonical. Original: {self:?}"
        );
        let x = derive_re::gfp(HashSet::new(), e, &c);
        // eprintln!("–––––––––––––––––––––––––––––––");
        // for (r, s) in &x {
        //     eprintln!("{r:?}");
        //     eprintln!("{s:?}");
        //     eprintln!("");
        // }
        // eprintln!("–––––––––––––––––––––––––––––––");
        let y = derive_re::gamma_set(&x);
        y
    }
    pub fn deriv_re_norm(&self, e: &Regex<C>) -> Regex<C>
    where
        C: Example + Realizable + Display,
        Char<C>: Pretty<()>,
    {
        self.deriv_re(e).to_dfa().minimized().to_regex()
    }
}

mod derive_re {
    use super::*;
    use std::{collections::HashSet, hash::Hash};

    pub fn gfp<C: Copy + Debug + Eq + Hash + Ord>(
        mut x: HashSet<(Regex<C>, Regex<C>)>,
        r: &Regex<C>,
        s: &Regex<C>,
    ) -> HashSet<(Regex<C>, Regex<C>)> {
        let r = &r.canonical();
        let s_simp = s.simplify();
        for (r1, s1) in &x {
            if r == r1 && &s_simp == s1 {
                return x;
            }
        }
        x.insert((r.clone(), s.simplify()));
        match r {
            Regex::Empty => x,
            Regex::Eps => x,
            Regex::Seq(r1, r2) => match r1.as_ref() {
                Regex::Char(c) => gfp(x, r2, &s.deriv(*c)),
                Regex::Or(r11, r12) => {
                    let x = gfp(x, &seq(r11.as_ref().clone(), r2.as_ref().clone()), s);
                    let x = gfp(x, &seq(r12.as_ref().clone(), r2.as_ref().clone()), s);
                    x
                }
                Regex::Star(r11) => {
                    let x = gfp(x, r2.as_ref(), s);
                    let x = gfp(
                        x,
                        &seq(
                            r11.as_ref().clone(),
                            seq(star(r11.as_ref().clone()), r2.as_ref().clone()),
                        ),
                        s,
                    );
                    x
                }
                _ => unreachable!(),
            },
            Regex::Char(_) => unreachable!(),
            Regex::Or(_, _) => unreachable!(),
            Regex::And(_, _) => unreachable!(),
            Regex::Star(_) => unreachable!(),
            Regex::Neg(_) => unreachable!(),
        }
    }

    pub fn gamma<C: Copy>(r: &Regex<C>, s: &Regex<C>) -> Regex<C> {
        match r {
            Regex::Eps => s.clone(),
            _ => neg(empty),
        }
    }

    pub fn gamma_set<C: Copy + Hash>(x: &HashSet<(Regex<C>, Regex<C>)>) -> Regex<C> {
        let mut e = neg(empty);
        for (r, s) in x {
            e = and(e, gamma(r, s))
        }
        e
    }
}

impl Regex<char> {
    pub fn to_u8(&self) -> Regex<u8> {
        match self {
            Regex::Empty => empty,
            Regex::Eps => eps,
            Regex::Char(c) => {
                let mut buf = [0u8; 4];
                c.encode_utf8(&mut buf);
                if buf[0] == 0 {
                    char_(0)
                } else if buf[1] == 0 {
                    char_(buf[0])
                } else if buf[2] == 0 {
                    seq(char_(buf[0]), char_(buf[1]))
                } else if buf[3] == 0 {
                    seq(char_(buf[0]), seq(char_(buf[1]), char_(buf[2])))
                } else {
                    seq(
                        char_(buf[0]),
                        seq(char_(buf[1]), seq(char_(buf[2]), char_(buf[3]))),
                    )
                }
            }
            Regex::Or(e1, e2) => or(e1.to_u8(), e2.to_u8()),
            Regex::And(e1, e2) => and(e1.to_u8(), e2.to_u8()),
            Regex::Seq(e1, e2) => seq(e1.to_u8(), e2.to_u8()),
            Regex::Star(e) => star(e.to_u8()),
            Regex::Neg(e) => neg(e.to_u8()),
        }
    }
}
