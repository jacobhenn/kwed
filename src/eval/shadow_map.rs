use std::{collections::HashMap, hash::Hash};

#[derive(Debug, Default, Clone)]
pub struct ShadowMap<K, V> {
    scopes: Vec<Vec<K>>,
    map: HashMap<K, Vec<V>>,
}

impl<K, V> ShadowMap<K, V> {
    pub fn new() -> Self {
        Self {
            scopes: vec![Vec::new()],
            map: HashMap::new(),
        }
    }

    // TODO: this can be implemented better
    pub fn insert(&mut self, k: K, v: V)
    where
        K: Clone + Eq + Hash,
    {
        self.scopes
            .last_mut()
            .expect("scopes should be nonempty")
            .push(k.clone());
        self.map.entry(k).or_insert(Vec::new()).push(v);
    }

    pub fn get(&self, k: &K) -> Option<&V>
    where
        K: Eq + Hash,
    {
        self.map
            .get(k)
            .map(|v| v.last().expect("entry should be nonempty"))
    }

    pub fn contains_key(&self, k: &K) -> bool
    where
        K: Eq + Hash,
    {
        self.map.contains_key(k)
    }

    // TODO: this could be more elegant
    pub fn remove(&mut self, k: &K) -> Option<V>
    where
        K: Eq + Hash,
    {
        if let Some(vs) = self.map.get_mut(k) {
            if vs.len() == 1 {
                self.map.remove(k).unwrap().pop()
            } else {
                Some(vs.pop().expect("entry should be nonempty"))
            }
        } else {
            None
        }
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    // TODO: how should this work?
    pub fn pop_scope(&mut self)
    where
        K: Eq + Hash,
    {
        if self.scopes.len() == 1 {
            println!("warning: something tried to pop the top scope");
            return;
        }

        for k in self.scopes.pop().expect("scopes should be nonempty") {
            self.remove(&k);
        }
    }
}
