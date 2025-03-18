use std::collections::HashSet;
use std::hash::Hash;

pub struct SubSetIter<T> {
    pub set: HashSet<T>,
    pub cur: usize,
    pub max: usize,
}

impl<T: Clone + Hash + Eq> SubSetIter<T> {
    pub fn from(set: HashSet<T>) -> Self {
        Self {
            cur: 0,
            max: 2usize.pow(set.len() as u32),
            set,
        }
    }
}

impl<T: Clone + Hash + Eq> Iterator for SubSetIter<T> {
    type Item = HashSet<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.max {
            let mut res = HashSet::new();
            let mut i = self.cur;
            for x in &self.set {
                let contained = i % 2 == 1;
                i = i / 2;
                if contained {
                    res.insert(x.clone());
                }
            }
            self.cur += 1;
            Some(res)
        } else {
            None
        }
    }
}
