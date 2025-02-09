#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirBasicBlockRef(usize);

impl MirBasicBlockRef {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn id(&self) -> usize {
        self.0
    }
}

#[derive(Debug)]
pub struct MirBasicBlock<'mir> {
    pub basic_block_id: MirBasicBlockRef,
    pub name: &'mir str,
}

impl<'mir> MirBasicBlock<'mir> {
    pub fn new(id: MirBasicBlockRef, name: &'mir str) -> Self {
        Self {
            basic_block_id: id,
            name,
        }
    }
}
