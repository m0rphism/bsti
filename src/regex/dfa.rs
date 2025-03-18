use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Display};
use std::hash::Hash;

use super::pattern::{Pattern, Realizable};

#[derive(Clone, Debug)]
pub struct DFA<C> {
    pub states: HashMap<usize, HashMap<C, usize>>,
    pub init: usize,
    pub finals: HashSet<usize>,
}

impl<C: Display + Hash + Ord> Display for DFA<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "init: {}\n", self.init)?;
        write!(f, "finals: {:?}\n", self.finals)?;
        write!(f, "states:\n")?;
        let mut states = self.states.iter().collect::<Vec<_>>();
        states.sort_by_key(|(k, _)| **k);
        for (s, tgts) in states {
            write!(f, "  {s}:\n")?;
            for (p, t) in tgts {
                write!(f, "    {t}: {p}\n")?;
            }
        }
        Ok(())
    }
}

impl<C: Copy + Debug + Eq + Hash + Display + Realizable> DFA<C> {
    pub fn minimize(&mut self) {
        self.remove_unreachable_states();
        self.remove_dead_states();
        self.merge_duplicate_states();
    }
    pub fn minimized(&self) -> Self {
        let mut dfa = self.clone();
        dfa.minimize();
        dfa
    }
    pub fn remove_unreachable_states(&mut self) {
        // Find reachable states
        let mut reachable = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(self.init);
        while let Some(s) = queue.pop_front() {
            if reachable.insert(s) {
                let tgts = self.states.get(&s).unwrap();
                for (_c, t) in tgts.iter() {
                    queue.push_back(*t);
                }
            }
        }

        // Remove unreachable states
        let keys = self.states.keys().cloned().collect::<Vec<_>>();
        for s in keys {
            if !reachable.contains(&s) {
                self.states.remove(&s);
            }
        }
        // Remove edges to unreachable states
        for tgts in self.states.values_mut() {
            *tgts = tgts
                .iter()
                .filter(|(_, tgt)| reachable.contains(tgt))
                .map(|(c, tgt)| (*c, *tgt))
                .collect::<HashMap<_, _>>();
        }
    }
    pub fn remove_dead_states(&mut self) {
        // Find alive states
        let mut alive = HashSet::new();
        let mut queue = VecDeque::new();
        queue.extend(self.finals.iter().cloned());
        while let Some(s) = queue.pop_front() {
            if alive.insert(s) {
                for (src, _) in self.sources(s) {
                    queue.push_back(src);
                }
            }
        }

        // Remove dead states if not init
        let keys = self.states.keys().cloned().collect::<Vec<_>>();
        for s in keys {
            if !alive.contains(&s) && s != self.init {
                self.states.remove(&s);
            }
        }

        // Remove edges to dead
        for tgts in self.states.values_mut() {
            let dead = tgts
                .iter()
                .filter_map(|(c, tgt)| if alive.contains(tgt) { None } else { Some(*c) })
                .collect::<HashSet<_>>();
            for d in dead {
                tgts.remove(&d);
            }
        }
    }
    // Doesnt account if a source has two edges to target!
    pub fn sources(&self, tgt: usize) -> HashSet<(usize, C)> {
        let mut srcs = HashSet::new();
        for (src, tgts) in &self.states {
            for (c, tgt2) in tgts {
                if tgt == *tgt2 {
                    srcs.insert((*src, *c));
                }
            }
        }
        srcs
    }
    pub fn merge_duplicate_states(&mut self) {
        // Build partitions of equivalent states
        let finals = self.finals.iter().cloned().collect::<BTreeSet<_>>();
        let states = self.states.keys().cloned().collect::<BTreeSet<_>>();
        let non_finals = states.difference(&finals).cloned().collect::<BTreeSet<_>>();

        let mut partitions = HashSet::from([finals.clone(), non_finals.clone()]);
        let mut queue = VecDeque::from([finals.clone(), non_finals.clone()]);

        while let Some(a) = queue.pop_front() {
            let mut a_srcs = HashSet::new();
            for s in a {
                a_srcs.extend(self.sources(s));
            }

            for c in Pattern::everything().realize() {
                let x = a_srcs
                    .iter()
                    .cloned()
                    .filter_map(|(s, c2)| if c2 == c { Some(s) } else { None })
                    .collect::<BTreeSet<_>>();
                let mut partitions2 = HashSet::new();
                for y in partitions {
                    let xy = x.intersection(&y).cloned().collect::<BTreeSet<_>>();
                    let yx = y.difference(&x).cloned().collect::<BTreeSet<_>>();
                    if !xy.is_empty() && !yx.is_empty() {
                        partitions2.insert(xy.clone());
                        partitions2.insert(yx.clone());
                        if let Some(i) = queue.iter().position(|x| x == &y) {
                            queue.remove(i);
                            queue.push_back(xy);
                            queue.push_back(yx);
                        } else {
                            if xy.len() <= yx.len() {
                                queue.push_back(xy);
                            } else {
                                queue.push_back(yx);
                            }
                        }
                    } else {
                        partitions2.insert(y);
                    }
                }
                partitions = partitions2;
            }
        }

        // Replace all equivalent state with a single representing state.
        for p in partitions {
            if p.len() > 1 {
                let mut it = p.into_iter();
                let winner = it.next().unwrap();
                let loosers = it.collect::<HashSet<_>>();
                for looser in &loosers {
                    self.states.remove(looser);
                }
                for tgts in self.states.values_mut() {
                    for tgt in tgts.values_mut() {
                        if loosers.contains(tgt) {
                            *tgt = winner;
                        }
                    }
                }
            }
        }
    }

    pub fn is_subseteq_of(&self, other: &Self) -> bool {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::from([(self.init, other.init)]);
        while let Some((s1, s2)) = queue.pop_front() {
            if visited.insert(s1) {
                if self.finals.contains(&s1) && !other.finals.contains(&s2) {
                    return false;
                }
                for (c, t1) in &self.states[&s1] {
                    if let Some(t2) = other.states[&s2].get(&c) {
                        queue.push_back((*t1, *t2));
                    } else {
                        return false;
                    }
                }
            }
        }
        true
    }
    pub fn is_equal_to(&self, other: &Self) -> bool {
        self.is_subseteq_of(other) && other.is_subseteq_of(self)
    }
}
