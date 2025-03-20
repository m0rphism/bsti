use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Graph<L: Eq + Hash> {
    pub edges: HashMap<L, HashSet<L>>,
}

impl<L: Clone + Eq + Hash + std::fmt::Debug> Graph<L> {
    pub fn empty() -> Self {
        Graph {
            edges: HashMap::new(),
        }
    }
    pub fn singleton(l: L) -> Self {
        let mut g = Graph::empty();
        g.edges.insert(l, HashSet::new());
        g
    }
    pub fn union(&self, other: &Graph<L>) -> Self {
        let mut out = self.clone();
        for (l, tgts) in &other.edges {
            let e = out.edges.entry(l.clone()).or_insert_with(|| HashSet::new());
            e.extend(tgts.into_iter().cloned());
        }
        out
    }
    pub fn plus(&self, other: &Graph<L>) -> Self {
        let mut out = self.union(other);
        for src in self.edges.keys() {
            for tgt in other.edges.keys() {
                out.edges.get_mut(src).unwrap().insert(tgt.clone());
            }
        }
        out
    }
    pub fn is_subgraph_of(&self, other: &Self) -> bool {
        for (src, tgts) in &self.edges {
            if let Some(tgts2) = &other.edges.get(src) {
                for tgt in tgts {
                    if !tgts2.contains(tgt) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        for src2 in other.edges.keys() {
            if !self.edges.contains_key(src2) {
                return false;
            }
        }
        true
    }
    pub fn is_reachable(&self, src: &L, tgt: &L) -> bool {
        let mut visited = HashSet::<&L>::new();
        let mut queue = VecDeque::new();
        queue.push_back(src);
        while let Some(src) = queue.pop_front() {
            if visited.insert(src) {
                if src == tgt {
                    return true;
                }
                for tgt in &self.edges[src] {
                    queue.push_back(tgt);
                }
            }
        }
        false
    }
}
