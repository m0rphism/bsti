use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;

use crate::regex::dfa::DFA;
use crate::regex::pattern::Pattern;
use crate::regex::regex::*;

#[derive(Clone, Debug)]
pub struct GNFA<C> {
    pub init: usize,
    pub final_: usize,
    pub states: HashMap<usize, HashMap<usize, Regex<C>>>,
}

impl<C: Copy + Debug + Eq + Hash + Display> GNFA<C> {
    pub fn remove_sources(&mut self, s: usize) -> HashMap<usize, Regex<C>> {
        let mut srcs = HashMap::new();
        for (src, tgts) in &mut self.states {
            if let Some(r) = tgts.remove(&s) {
                srcs.insert(*src, r);
            }
        }
        srcs
    }
    pub fn to_regex(self) -> Regex<C> {
        let mut a = self;
        while a.states.len() > 2 {
            let s = *a
                .states
                .keys()
                .find(|k| **k != a.init && **k != a.final_)
                .unwrap();
            let mut tgts = a.states.remove(&s).unwrap();
            let srcs = a.remove_sources(s);
            let loop_r = tgts.remove(&s).map(star);
            for (src, src_r) in &srcs {
                for (tgt, tgt_r) in &tgts {
                    let r = if let Some(loop_r) = &loop_r {
                        seq(src_r.clone(), seq(loop_r.clone(), tgt_r.clone()))
                    } else {
                        seq(src_r.clone(), tgt_r.clone())
                    };
                    // a.states.get_mut(src).unwrap().insert(*tgt, r);
                    let r2 = r.clone();
                    a.states
                        .get_mut(src)
                        .unwrap()
                        .entry(*tgt)
                        .and_modify(|v| *v = or(v.clone(), r))
                        .or_insert(r2);
                }
            }
        }
        a.states[&a.init].iter().next().unwrap().1.clone()
    }
}

impl<C: Copy + Debug + Eq + Hash + Display> DFA<C> {
    pub fn next_free_state(&self) -> usize {
        self.states.keys().max().map(|i| *i + 1).unwrap_or(0)
    }
    pub fn to_gnfa(&self) -> GNFA<C> {
        let init = self.next_free_state();
        let final_ = init + 1;
        let mut states = HashMap::new();
        for (s, tgts) in &self.states {
            let mut tgts_out = HashMap::new();
            if self.finals.contains(s) {
                tgts_out.insert(final_, eps);
            }
            for (c, tgt) in tgts {
                tgts_out
                    .entry(*tgt)
                    .and_modify(|v| *v = or(v.clone(), char_(*c)))
                    .or_insert(char_(*c));
            }
            states.insert(*s, tgts_out);
        }

        states.insert(final_, HashMap::new());

        let mut init_tgts = HashMap::new();
        init_tgts.insert(self.init, eps);
        states.insert(init, init_tgts);

        let keys = states.keys().cloned().collect::<Vec<_>>();
        for k1 in keys {
            for (k2, tgts) in &mut states {
                if *k2 != final_ && k1 != init {
                    tgts.entry(k1).or_insert_with(|| Regex::Empty);
                }
            }
        }

        GNFA {
            init,
            final_,
            states,
        }
    }
    pub fn to_regex(&self) -> Regex<C> {
        self.to_gnfa().to_regex()
    }
}

// TODO: Unused
impl<C: Copy + Debug + Eq + Hash + Display> Pattern<C> {
    pub fn to_regex(&self) -> Regex<C> {
        let mut r = empty;
        for c in &self.chars {
            r = or(r, char_(*c));
        }
        if !self.positive {
            r = neg(r);
        }
        r
    }
}
