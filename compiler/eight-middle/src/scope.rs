use eight_support::ice;
use std::collections::{BTreeMap, VecDeque};

#[derive(Debug)]
pub struct Scope<K, V> {
    scopes: VecDeque<BTreeMap<K, V>>,
}

impl<K: Ord, V> Default for Scope<K, V> {
    fn default() -> Self {
        Self {
            scopes: VecDeque::new(),
        }
    }
}

impl<K: Ord, V> Scope<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a new scope onto the deque.
    pub fn enter_scope(&mut self) {
        let scope = BTreeMap::new();
        self.scopes.push_front(scope);
    }

    /// Pop the topmost scope from the deque.
    pub fn leave_scope(&mut self) {
        self.scopes.pop_front();
    }

    /// Get the current depth from the global scope that we are currently in.
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// Find an item in the context.
    pub fn find(&self, name: &K) -> Option<&V> {
        for scope in &self.scopes {
            if let Some(item) = scope.get(name) {
                return Some(item);
            }
        }
        None
    }

    pub fn find_within_depth(&self, name: &K, depth: usize) -> Option<&V> {
        for (index, scope) in self.scopes.iter().rev().enumerate() {
            if index == depth - 1 {
                return scope.get(name);
            }
        }
        None
    }

    pub fn add(&mut self, name: K, id: V) {
        let scope = self
            .scopes
            .front_mut()
            .unwrap_or_else(|| ice!("local context has no scope"));
        scope.insert(name, id);
    }

    pub fn remove(&mut self, name: &K) {
        let scope = self
            .scopes
            .front_mut()
            .unwrap_or_else(|| ice!("local context has no scope"));
        scope.remove(name);
    }
}

#[cfg(test)]
mod tests {
    use super::Scope;
    use eight_macros::assert_none;

    #[test]
    fn test_local_context_interleaving() {
        let mut resolver = Scope::<&'static str, i32>::new();
        assert_eq!(resolver.depth(), 0);
        resolver.enter_scope();
        resolver.add("a", 1);
        assert_eq!(resolver.depth(), 1);
        resolver.enter_scope();
        assert_eq!(Some(&1), resolver.find(&"a"));
        resolver.add("a", 2);
        assert_eq!(Some(&2), resolver.find(&"a"));
        resolver.leave_scope();
        assert_eq!(Some(&1), resolver.find(&"a"));
        resolver.leave_scope();
        assert_eq!(resolver.depth(), 0);
    }

    #[test]
    fn test_local_context_removal() {
        let mut resolver = Scope::<&'static str, i32>::new();
        resolver.enter_scope();
        resolver.add("a", 1);
        assert_eq!(Some(&1), resolver.find(&"a"));
        resolver.remove(&"a");
        assert_none!(resolver.find(&"a"));
    }
}
