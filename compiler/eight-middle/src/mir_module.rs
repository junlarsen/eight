use crate::context::CompileContext;
use crate::mir::{MirFunctionRef, MirFunctionType};
use crate::mir_function::MirFunction;
use eight_diagnostics::ice;
use std::collections::BTreeMap;

/// A module in the MIR representation.
///
/// A module holds definitions for all functions and global values in a translation unit. It assumes
/// that functions with an empty body are external and to be resolved at link time.
#[derive(Debug, Default)]
pub struct MirModule<'mir> {
    data: MirModuleData<'mir>,
    interface: MirModuleInterface<'mir>,
}

impl<'mir> MirModule<'mir> {
    pub fn new(data: MirModuleData<'mir>, interface: MirModuleInterface<'mir>) -> Self {
        Self { data, interface }
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }

    pub fn interface(&self) -> &MirModuleInterface<'mir> {
        &self.interface
    }
}

/// The public API interface for a MIR module.
#[derive(Debug, Default)]
pub struct MirModuleInterface<'mir> {
    functions: BTreeMap<&'mir str, &'mir MirFunctionType<'mir>>,
}

impl<'mir> MirModuleInterface<'mir> {
    pub fn insert_function(&mut self, name: &'mir str, ty: &'mir MirFunctionType<'mir>) {
        // TODO: Check for collisions
        self.functions.insert(name, ty);
    }

    pub fn get_function(&self, name: &'mir str) -> Option<&'mir MirFunctionType<'mir>> {
        self.functions.get(name).copied()
    }
}

/// The data for a MIR module.
///
/// Because the MIR is a possibly cyclic graph, we don't want to pass around references to the
/// actual data, instead we pass around references that can acquire information about the item they
/// point to through the MirModuleData.
#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    functions: BTreeMap<&'mir str, MirFunction<'mir>>,
}
impl<'mir> MirModuleData<'mir> {
    pub fn functions(&self) -> impl Iterator<Item = &MirFunction<'mir>> {
        self.functions.values()
    }

    pub fn get_function(&self, name: &'mir str) -> Option<&MirFunction<'mir>> {
        self.functions.get(name)
    }
}

pub struct MirModuleContext<'mir> {
    cc: &'mir CompileContext<'mir>,
    data: MirModuleData<'mir>,
}

impl<'mir> MirModuleContext<'mir> {
    pub fn new(cc: &'mir CompileContext<'mir>) -> Self {
        Self {
            cc,
            data: MirModuleData::default(),
        }
    }

    pub fn build(self, interface: MirModuleInterface<'mir>) -> MirModule<'mir> {
        MirModule::new(self.data, interface)
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }

    /// Provide the completed MIR function.
    pub fn insert_function(&mut self, id: MirFunctionRef<'mir>, fun: MirFunction<'mir>) {
        if self.data.functions.contains_key(&id) {
            ice!("function already implemented");
        }
        self.data.functions.insert(id, fun);
    }
}
