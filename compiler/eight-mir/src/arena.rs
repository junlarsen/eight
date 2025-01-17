use bumpalo::Bump;
use eight_middle::arena::StringInterner;
use std::rc::Rc;

pub struct MirArena<'arena> {
    allocator: Rc<Bump>,
    name_arena: StringInterner<'arena>,
}

impl<'arena> Default for MirArena<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'arena> MirArena<'arena> {
    pub fn new() -> Self {
        let allocator = Rc::new(Bump::new());
        Self {
            name_arena: StringInterner::new(allocator.clone()),
            allocator,
        }
    }

    pub fn names(&'arena self) -> &'arena StringInterner<'arena> {
        &self.name_arena
    }
}
