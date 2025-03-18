use std::collections::HashSet;
use std::fmt::Display;
use std::hash::Hash;

#[derive(Clone, Debug)]
pub struct Pattern<C> {
    pub chars: HashSet<C>,
    pub positive: bool,
}

#[derive(Clone, Debug)]
pub struct PatternSplit<C> {
    pub only_left: Pattern<C>,
    pub only_right: Pattern<C>,
    pub both: Pattern<C>,
}

impl<C: Eq + Hash + Clone> Pattern<C> {
    pub fn new(chars: HashSet<C>, positive: bool) -> Self {
        Pattern { chars, positive }
    }
    pub fn from(chars: impl IntoIterator<Item = C>, positive: bool) -> Self {
        Pattern::new(chars.into_iter().collect(), positive)
    }
    pub fn positive(cs: HashSet<C>) -> Self {
        Pattern::new(cs, true)
    }
    pub fn negative(cs: HashSet<C>) -> Self {
        Pattern::new(cs, false)
    }
    pub fn positive_from(cs: impl IntoIterator<Item = C>) -> Self {
        Pattern::from(cs, true)
    }
    pub fn negative_from(cs: impl IntoIterator<Item = C>) -> Self {
        Pattern::from(cs, false)
    }
    pub fn char(c: C, positive: bool) -> Self {
        let mut chars = HashSet::new();
        chars.insert(c);
        Pattern::new(chars, positive)
    }
    pub fn positive_char(c: C) -> Self {
        Pattern::char(c, true)
    }
    pub fn negative_char(c: C) -> Self {
        Pattern::char(c, false)
    }
    pub fn everything() -> Self {
        Pattern::new(HashSet::new(), false)
    }
    pub fn nothing() -> Self {
        Pattern::new(HashSet::new(), true)
    }
    pub fn matches(&self, c: &C) -> bool {
        if self.positive {
            self.chars.contains(c)
        } else {
            !self.chars.contains(c)
        }
    }
    pub fn union(&self, other: &Pattern<C>) -> Pattern<C> {
        match (self.positive, other.positive) {
            (true, true) => Pattern::new(self.chars.union(&other.chars).cloned().collect(), true),
            (true, false) => Pattern::new(
                other.chars.difference(&self.chars).cloned().collect(),
                false,
            ),
            (false, true) => Pattern::new(
                self.chars.difference(&other.chars).cloned().collect(),
                false,
            ),
            (false, false) => Pattern::new(
                self.chars.intersection(&other.chars).cloned().collect(),
                false,
            ),
        }
    }
    pub fn intersection(&self, other: &Pattern<C>) -> Pattern<C> {
        match (self.positive, other.positive) {
            (true, true) => Pattern::new(
                self.chars.intersection(&other.chars).cloned().collect(),
                true,
            ),
            (true, false) => {
                Pattern::new(self.chars.difference(&other.chars).cloned().collect(), true)
            }
            (false, true) => {
                Pattern::new(other.chars.difference(&self.chars).cloned().collect(), true)
            }
            (false, false) => {
                Pattern::new(self.chars.union(&other.chars).cloned().collect(), false)
            }
        }
    }
    pub fn negate(&self) -> Pattern<C> {
        Pattern::new(self.chars.clone(), !self.positive)
    }
    /// Split two patterns into three disjoint patterns.
    pub fn split(&self, other: &Pattern<C>) -> PatternSplit<C> {
        match (self.positive, other.positive) {
            (true, true) => PatternSplit {
                only_left: Pattern::new(
                    self.chars.difference(&other.chars).cloned().collect(),
                    true,
                ),
                only_right: Pattern::new(
                    other.chars.difference(&self.chars).cloned().collect(),
                    true,
                ),
                both: Pattern::new(
                    self.chars.intersection(&other.chars).cloned().collect(),
                    true,
                ),
            },
            (true, false) => PatternSplit {
                only_left: Pattern::new(
                    self.chars.intersection(&other.chars).cloned().collect(),
                    true,
                ),
                only_right: Pattern::new(other.chars.union(&self.chars).cloned().collect(), false),
                both: Pattern::new(self.chars.difference(&other.chars).cloned().collect(), true),
            },
            (false, true) => PatternSplit {
                only_left: Pattern::new(other.chars.union(&self.chars).cloned().collect(), false),
                only_right: Pattern::new(
                    self.chars.intersection(&other.chars).cloned().collect(),
                    true,
                ),
                both: Pattern::new(other.chars.difference(&self.chars).cloned().collect(), true),
            },
            (false, false) => PatternSplit {
                only_left: Pattern::new(
                    other.chars.difference(&self.chars).cloned().collect(),
                    true,
                ),
                only_right: Pattern::new(
                    self.chars.difference(&other.chars).cloned().collect(),
                    true,
                ),
                both: Pattern::new(self.chars.union(&other.chars).cloned().collect(), false),
            },
        }
    }
    /// Underapproximation of wether the pattern matches nothing.
    pub fn is_definitely_nothing(&self) -> bool {
        self.positive && self.chars.is_empty()
    }
}

pub fn cartesian_intersection<C: Hash + Eq + Clone>(
    ps1: Vec<Pattern<C>>,
    ps2: Vec<Pattern<C>>,
) -> Vec<Pattern<C>> {
    let mut ps = vec![];
    for p1 in &ps1 {
        for p2 in &ps2 {
            let p = p1.intersection(p2);
            if !p.is_definitely_nothing() {
                ps.push(p);
            }
        }
    }
    ps
}

impl<C: Display + Ord> Display for Pattern<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pre = if self.positive { "" } else { "^" };
        write!(f, "[{}", pre)?;
        let mut cs: Vec<_> = self.chars.iter().collect();
        cs.sort();
        for c in cs {
            write!(f, "{}", c)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

pub trait Realizable: Sized {
    fn realize(p: &Pattern<Self>) -> HashSet<Self>;
}

impl<C: Realizable> Pattern<C> {
    pub fn realize(&self) -> HashSet<C> {
        C::realize(&self)
    }
}

impl Realizable for u8 {
    fn realize(p: &Pattern<Self>) -> HashSet<Self> {
        if p.positive {
            p.chars.clone()
        } else {
            let mut chars = HashSet::new();
            for c in 0..=255 {
                if !p.chars.contains(&c) {
                    chars.insert(c);
                }
            }
            chars
        }
    }
}

pub trait Example: Sized {
    fn example(p: &Pattern<Self>) -> Option<Self>;
}

impl<C: Example> Pattern<C> {
    pub fn example(&self) -> Option<C> {
        C::example(&self)
    }
}

impl Example for u8 {
    fn example(p: &Pattern<u8>) -> Option<u8> {
        if p.positive {
            p.chars.iter().next().copied()
        } else {
            if p.chars.len() == 256 {
                None
            } else {
                let mut c = 0;
                while p.chars.contains(&c) {
                    c += 1;
                }
                Some(c)
            }
        }
    }
}

impl Example for char {
    fn example(p: &Pattern<char>) -> Option<char> {
        if p.positive {
            p.chars.iter().next().copied()
        } else {
            let mut i = 0;
            while i < u32::MAX {
                if let Some(c) = char::from_u32(i) {
                    if !p.chars.contains(&c) {
                        return Some(c);
                    } else {
                        i += 1;
                    }
                } else {
                    i += 1;
                }
            }
            None
        }
    }
}

pub trait Finite: Sized {
    fn is_empty(p: &Pattern<Self>) -> bool;
}

impl Finite for u8 {
    fn is_empty(p: &Pattern<Self>) -> bool {
        p.positive && p.chars.len() == 0 || !p.positive && p.chars.len() == 256
    }
}

// FIXME: we need to get an exhaustive list of unicode chars or remove patterns...
// impl Finite for char {
//     fn is_empty(p: &Pattern<Self>) -> bool {
//         p.positive && p.chars.len() == 0
//     }
// }
