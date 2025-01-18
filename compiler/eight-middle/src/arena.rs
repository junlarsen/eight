use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

/// A general purpose string interner.
pub struct StringInterner<'arena> {
    allocator: Rc<Bump>,
    intern: RefCell<HashSet<&'arena str>>,
}

impl<'arena> StringInterner<'arena> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashSet::new()),
        }
    }

    /// Intern the given name into the interner.
    pub fn get(&'arena self, name: &str) -> &'arena str {
        if let Some(interned) = self.intern.borrow().get(name) {
            return interned;
        }
        let id = self.allocator.alloc_str(name);
        self.intern.borrow_mut().insert(id);
        id
    }

    /// Shorthand for getting the name of usize as a &str.
    pub fn get_usize(&'arena self, id: usize) -> &'arena str {
        self.get(&id.to_string())
    }
}
