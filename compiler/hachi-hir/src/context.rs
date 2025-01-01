use std::collections::{BTreeMap, VecDeque};

/// A deque-based scoped context.
#[derive(Debug)]
pub struct LocalContext<T> {
    scopes: VecDeque<BTreeMap<String, T>>,
}

impl<T> Default for LocalContext<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LocalContext<T> {
    pub fn new() -> Self {
        LocalContext {
            scopes: VecDeque::new(),
        }
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

    pub fn find(&self, name: &str) -> Option<&T> {
        for scope in &self.scopes {
            if let Some(item) = scope.get(name) {
                return Some(item);
            }
        }
        None
    }

    pub fn add(&mut self, name: &str, id: T) {
        let scope = self
            .scopes
            .front_mut()
            .expect("ReferenceResolver::add: no scope");
        scope.insert(name.to_string(), id);
    }

    pub fn remove(&mut self, name: &str) {
        let scope = self
            .scopes
            .front_mut()
            .expect("ReferenceResolver::remove: no scope");
        scope.remove(name);
    }

    pub fn local_size(&self) -> usize {
        self.scopes.front().map(|s| s.len()).unwrap_or(0)
    }

    pub fn find_local(&self, name: &str) -> Option<&T> {
        self.scopes.front().and_then(|s| s.get(name))
    }
}

#[cfg(test)]
mod tests {
    use super::LocalContext;
    use hachi_macros::assert_none;

    #[test]
    fn test_local_context_interleaving() {
        let mut resolver = LocalContext::<i32>::new();
        assert_eq!(resolver.depth(), 0);
        resolver.enter_scope();
        resolver.add("a", 1);
        assert_eq!(resolver.depth(), 1);
        resolver.enter_scope();
        assert_eq!(Some(&1), resolver.find("a"));
        resolver.add("a", 2);
        assert_eq!(Some(&2), resolver.find("a"));
        resolver.leave_scope();
        assert_eq!(Some(&1), resolver.find("a"));
        resolver.leave_scope();
        assert_eq!(resolver.depth(), 0);
    }

    #[test]
    fn test_local_context_removal() {
        let mut resolver = LocalContext::<i32>::new();
        resolver.enter_scope();
        resolver.add("a", 1);
        assert_eq!(Some(&1), resolver.find("a"));
        resolver.remove("a");
        assert_none!(resolver.find("a"));
    }
}
