use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;

use super::dfa::DFA;
use super::pattern;
use super::pattern::{Example, Pattern, Realizable};
use super::regex::Regex;

impl<C: Copy + Debug + Eq + Hash + Ord + Display + Example + Realizable> Regex<C> {
    pub fn to_dfa(&self) -> DFA<C> {
        let init = 0;
        let mut finals = HashSet::new();
        let mut states = HashMap::new();
        states.insert(init, HashMap::new());
        let mut cache = HashMap::new();
        let e = self.simplify();
        cache.insert(e.clone(), init);
        e.to_dfa_(init, &mut states, &mut finals, &mut cache);
        DFA {
            init,
            finals,
            states,
        }
    }
    fn to_dfa_(
        &self,
        cur_state: usize,
        states: &mut HashMap<usize, HashMap<C, usize>>,
        finals: &mut HashSet<usize>,
        cache: &mut HashMap<Regex<C>, usize>,
    ) {
        if self.nullable() {
            finals.insert(cur_state);
        }
        for p in self.partitions() {
            if let Some(c) = p.example() {
                let e = self.deriv(c).simplify();
                let mut is_new = false;
                let tgt_state = *cache.entry(e.clone()).or_insert_with(|| {
                    let i = states.len();
                    states.insert(i, HashMap::new());
                    is_new = true;
                    i
                });
                for c in p.realize() {
                    states.get_mut(&cur_state).unwrap().insert(c, tgt_state);
                }
                if is_new {
                    e.to_dfa_(tgt_state, states, finals, cache);
                }
            }
        }
    }

    pub fn partitions(&self) -> Vec<Pattern<C>> {
        match self {
            Regex::Empty => vec![Pattern::everything()],
            Regex::Eps => vec![Pattern::everything()],
            Regex::Char(c) => vec![
                Pattern::positive_char(c.clone()),
                Pattern::negative_char(c.clone()),
            ],
            Regex::Or(e1, e2) => pattern::cartesian_intersection(e1.partitions(), e2.partitions()),
            Regex::And(e1, e2) => pattern::cartesian_intersection(e1.partitions(), e2.partitions()),
            Regex::Seq(e1, e2) if e1.nullable() => {
                pattern::cartesian_intersection(e1.partitions(), e2.partitions())
            }
            Regex::Seq(e1, _) => e1.partitions(),
            Regex::Star(e) => e.partitions(),
            Regex::Neg(e) => e.partitions(),
        }
    }

    pub fn is_subseteq_of(&self, other: &Self) -> bool {
        let mut dfa1 = self.to_dfa();
        dfa1.minimize();
        let mut dfa2 = other.to_dfa();
        dfa2.minimize();
        dfa1.is_subseteq_of(&dfa2)
    }
    pub fn is_equal_to(&self, other: &Self) -> bool {
        let mut dfa1 = self.to_dfa();
        dfa1.minimize();
        let mut dfa2 = other.to_dfa();
        dfa2.minimize();
        dfa1.is_equal_to(&dfa2)
    }
}
