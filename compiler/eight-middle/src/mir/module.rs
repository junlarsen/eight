use crate::mir::function::{MirFunction, MirFunctionId};
use crate::mir::ty::MirFunctionType;
use std::collections::BTreeMap;

#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    pub functions: BTreeMap<MirFunctionId, MirFunction<'mir>>,
    pub function_types: BTreeMap<MirFunctionId, &'mir MirFunctionType<'mir>>,
    pub function_names: BTreeMap<MirFunctionId, &'mir str>,
    pub function_names_reverse: BTreeMap<&'mir str, MirFunctionId>,
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
    pub fn new(data: MirModuleData<'mir>) -> Self {
        Self { data }
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }
}
