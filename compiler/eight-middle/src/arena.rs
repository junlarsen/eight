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

    pub fn get(&'arena self, name: &str) -> &'arena str {
        if let Some(interned) = self.intern.borrow().get(name) {
            return interned;
        }
        let id = self.allocator.alloc_str(name);
        self.intern.borrow_mut().insert(id);
        id
    }
}
