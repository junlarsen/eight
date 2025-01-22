use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

/// A typed interner with a keyed type.
///
/// All values in the interner are owned by the allocator. These are backed by a hashmap. The type
/// is not thread-safe.
///
/// SAFETY: The RefCell here is safe, because the map can only be mutably borrowed once for each
/// entry in the map.
pub struct TypedInterner<'a, K, V> {
    allocator: Rc<Bump>,
    intern: RefCell<HashMap<K, &'a V>>,
}

impl<'a, K: Hash + Eq, V> TypedInterner<'a, K, V> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashMap::new()),
        }
    }

    /// Get a reference to the interned value by key, or insert it with the given function if it
    /// does not exist.
    ///
    /// This method should probably not be used directly, but the owner of the TypedInterner should
    /// provide helper methods for the cases, such as computing a HirPointerTy given the inner type.
    pub fn get_interned(&'a self, key: K, value: V) -> &'a V {
        self.intern
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| self.allocator.alloc(value))
    }
}

/// A general purpose string interner.
///
/// This string interner is shared across the entire middle-end of the compiler. It is primarily
/// used for interning identifiers in the HIR and local names in the MIR.
pub struct StringInterner<'a> {
    allocator: Rc<Bump>,
    intern: RefCell<HashSet<&'a str>>,
}

impl<'a> StringInterner<'a> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashSet::new()),
        }
    }

    /// Intern the given name into the interner.
    pub fn get(&'a self, name: &str) -> &'a str {
        if let Some(interned) = self.intern.borrow().get(name) {
            return interned;
        }
        let id = self.allocator.alloc_str(name);
        self.intern.borrow_mut().insert(id);
        id
    }

    /// Shorthand for getting the name of usize as a &str.
    pub fn get_usize(&'a self, id: usize) -> &'a str {
        self.get(&id.to_string())
    }
}
