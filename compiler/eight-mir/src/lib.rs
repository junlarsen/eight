use crate::function::MirFunction;
use crate::instruction::MirInstructionId;
use crate::ty::MirFunctionType;
use std::collections::BTreeMap;
use std::ops::Deref;

pub mod arena;
pub mod builder;
pub mod error;
pub mod function;
pub mod hir_lowering_pass;
pub mod instruction;
pub mod textual_pass;
pub mod ty;
pub mod value;

#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    functions: BTreeMap<MirFunctionId, MirFunction<'mir>>,
    function_types: BTreeMap<MirFunctionId, &'mir MirFunctionType<'mir>>,
    function_names: BTreeMap<MirFunctionId, &'mir str>,
    function_names_reverse: BTreeMap<&'mir str, MirFunctionId>,
}

impl<'mir> MirModuleData<'mir> {
    pub fn functions(&self) -> impl Iterator<Item = &MirFunction<'mir>> {
        self.functions.values()
    }

    pub fn get_function_by_id(&self, id: MirFunctionId) -> Option<&MirFunction<'mir>> {
        self.functions.get(&id)
    }

    pub fn get_function_by_name(&self, name: &'mir str) -> Option<&MirFunction<'mir>> {
        self.functions.get(self.function_names_reverse.get(name)?)
    }

    /// Get the function id for the given name.
    pub fn get_function_id(&self, name: &'mir str) -> Option<MirFunctionId> {
        self.function_names_reverse.get(name).copied()
    }

    /// Get the function name for the given id.
    pub fn get_function_name(&self, id: MirFunctionId) -> Option<&'mir str> {
        self.function_names.get(&id).copied()
    }

    /// Get the function type for the given id.
    pub fn get_function_type(&self, id: MirFunctionId) -> Option<&'mir MirFunctionType<'mir>> {
        self.function_types.get(&id).copied()
    }
}

#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    data: MirModuleData<'mir>,
}

impl<'mir> MirModule<'mir> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirFunctionId(pub usize);

impl Deref for MirFunctionId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct MirBasicBlockId(pub usize);

impl Deref for MirBasicBlockId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
pub struct MirBasicBlock<'mir> {
    pub name: &'mir str,
    pub instructions: Vec<MirInstructionId>,
}

impl<'mir> MirBasicBlock<'mir> {
    pub fn insert(&mut self, instruction: MirInstructionId) {
        self.instructions.push(instruction);
    }
}
