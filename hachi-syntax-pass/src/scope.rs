use std::collections::{BTreeMap, VecDeque};

/// A deque-based reference resolver.
///
/// Upon entering a new scope, the resolver will create a new scope and push it onto the deque. The
/// owner can then traverse a syntax tree or similar to store and resolve references in the scope.
#[cfg_attr(test, derive(Debug))]
pub struct ReferenceResolver<'p, T> {
    scopes: VecDeque<BTreeMap<&'p str, T>>,
}

impl<'p, T> Default for ReferenceResolver<'p, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'p, T> ReferenceResolver<'p, T> {
    pub fn new() -> Self {
        ReferenceResolver {
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

    pub fn add(&mut self, name: &'p str, id: T) {
        let scope = self
            .scopes
            .front_mut()
            .expect("ReferenceResolver::add: no scope");
        scope.insert(name, id);
    }

    pub fn remove(&mut self, name: &'p str) {
        let scope = self
            .scopes
            .front_mut()
            .expect("ReferenceResolver::remove: no scope");
        scope.remove(name);
    }
}

#[cfg(test)]
mod tests {
    use crate::scope::ReferenceResolver;
    use hachi_macros::assert_none;

    #[test]
    fn test_reference_resolver_interleaving() {
        let mut resolver = ReferenceResolver::<'_, i32>::new();
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
    fn test_reference_resolver_removal() {
        let mut resolver = ReferenceResolver::<'_, i32>::new();
        resolver.enter_scope();
        resolver.add("a", 1);
        assert_eq!(Some(&1), resolver.find("a"));
        resolver.remove("a");
        assert_none!(resolver.find("a"));
    }
}
