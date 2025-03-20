use std::collections::HashMap;

use crate::{
    syntax::{Id, Session},
    util::pretty::pretty_def,
};

#[derive(Debug, Clone)]
pub struct Rep {
    pub map: HashMap<Id, Session>,
}

impl Rep {
    pub fn empty() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
    pub fn single(id: Id, s: Session) -> Self {
        Self {
            map: HashMap::from([(id, s)]),
        }
    }
    pub fn join(&self, u: &Self) -> Self {
        let mut map = self.map.clone();
        for (x, s2) in &u.map {
            if let Some(s1) = map.get_mut(x) {
                *s1 = s1.join(&s2);
            } else {
                map.insert(x.clone(), s2.clone());
            }
        }
        Self { map }
    }
    pub fn remove_mut(&mut self, x: &Id) {
        let _ = self.map.remove(x);
    }
    pub fn remove(&self, x: &Id) -> Rep {
        let mut u = self.clone();
        u.remove_mut(x);
        u
    }
    pub fn eq(&self, u: &Self) -> bool {
        for (x, s1) in &self.map {
            if let Some(s2) = u.map.get(x) {
                if !s1.eq(s2) {
                    return false;
                }
            } else {
                return false;
            }
        }
        for x in u.map.keys() {
            if !self.map.contains_key(x) {
                return false;
            }
        }
        return true;
    }
}
