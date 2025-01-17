use crate::MirType;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum MirInstruction {
    Load(MirLoadInstruction),
}

/// The `mem.load` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirLoadInstruction {
    pub ty: MirType,
}

/// The `mem.store` instruction.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirStoreInstruction {
    pub ty: MirType,
}
