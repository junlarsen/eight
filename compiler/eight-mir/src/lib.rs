use crate::ty::MirFunctionType;
use instruction::MirInstruction;
use std::collections::BTreeMap;

pub mod arena;
pub mod builder;
pub mod error;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod ty;
pub mod value;

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    pub functions: BTreeMap<&'mir str, MirFunction<'mir>>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
pub struct MirFunction<'mir> {
    pub name: &'mir str,
    pub ty: &'mir MirFunctionType<'mir>,
    pub basic_blocks: Vec<MirBlock<'mir>>,
}

impl<'mir> MirFunction<'mir> {
    pub fn is_external(&self) -> bool {
        self.basic_blocks.is_empty()
    }
}

#[derive(Debug)]
pub struct MirBlock<'mir> {
    pub name: &'mir str,
    pub instructions: Vec<MirInstruction<'mir>>,
}
