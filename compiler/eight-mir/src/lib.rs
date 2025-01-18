use eight_middle::LinkageType;
use instruction::MirInstruction;
use std::collections::BTreeMap;

pub mod arena;
pub mod error;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod value;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    pub structs: BTreeMap<&'mir str, MirStruct<'mir>>,
    pub functions: BTreeMap<&'mir str, MirFunction<'mir>>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirFunction<'mir> {
    pub name: &'mir str,
    pub arguments: Vec<(&'mir str, MirType)>,
    pub return_type: MirType,
    pub basic_blocks: Vec<MirBlock<'mir>>,
    pub linkage_type: LinkageType,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirStruct<'mir> {
    pub name: &'mir str,
    pub fields: Vec<(&'mir str, MirType)>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub struct MirBlock<'mir> {
    pub name: &'mir str,
    pub instructions: Vec<MirInstruction<'mir>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Debug)]
pub enum MirType {
    Integer32,
    Bool,
    Void,
    Pointer,
    Struct { fields: Vec<MirType> },
}
