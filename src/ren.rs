use std::collections::HashMap;

use crate::syntax::Id;

#[derive(Debug, Clone)]
pub struct Ren {
    pub map: HashMap<Id, Id>,
}

impl Ren {
    pub fn empty() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
    pub fn single(x: Id, y: Id) -> Self {
        Self {
            map: HashMap::from([(x, y)]),
        }
    }
    pub fn join(&self, r: &Self) -> Self {
        let mut map = HashMap::new();
        for (x, y) in &self.map {
            if let Some(z) = r.map.get(y) {
                map.insert(x.clone(), z.clone());
            } else {
                map.insert(x.clone(), y.clone());
            }
        }
        for (x, y) in &r.map {
            if self.map.get(x).is_none() {
                map.insert(x.clone(), y.clone());
            }
        }
        Self { map }
    }
    pub fn remove_mut(&mut self, x: &Id) {
        let _ = self.map.remove(x);
    }
    pub fn remove(&self, x: &Id) -> Self {
        let mut r = self.clone();
        r.remove_mut(x);
        r
    }

    pub fn fresh_from<'a>(dom: impl IntoIterator<Item = &'a Id>, suffix: &str) -> Ren {
        let mut map = HashMap::new();
        for x in dom {
            map.insert(x.clone(), format!("{x}::{suffix}"));
        }
        Self { map }
    }

    pub fn invert(&self) -> Self {
        let mut map = HashMap::new();
        for (x, y) in &self.map {
            map.insert(y.clone(), x.clone());
        }
        Self { map }
    }
}
