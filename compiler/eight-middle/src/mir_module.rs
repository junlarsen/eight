use crate::context::CompileContext;
use crate::hir::HirModule;
use crate::mir::MirFunctionType;
use crate::mir_function::{MirFunction, MirFunctionRef};
use eight_diagnostics::ice;
use std::collections::BTreeMap;

/// A module in the MIR representation.
///
/// A module holds definitions for all functions and global values in a translation unit. It assumes
/// that functions with an empty body are external and to be resolved at link time.
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

/// The data for a MIR module.
///
/// Because the MIR is a possibly cyclic graph, we don't want to pass around references to the
/// actual data, instead we pass around references that can acquire information about the item they
/// point to through the MirModuleData.
#[derive(Debug, Default)]
pub struct MirModuleData<'mir> {
    functions: BTreeMap<MirFunctionRef, MirFunction<'mir>>,
    function_types: BTreeMap<MirFunctionRef, &'mir MirFunctionType<'mir>>,
    function_names: BTreeMap<MirFunctionRef, &'mir str>,
    function_names_reverse: BTreeMap<&'mir str, MirFunctionRef>,
}
impl<'mir> MirModuleData<'mir> {
    pub fn functions(&self) -> impl Iterator<Item = &MirFunction<'mir>> {
        self.functions.values()
    }

    pub fn get_function_by_id(&self, id: MirFunctionRef) -> Option<&MirFunction<'mir>> {
        self.functions.get(&id)
    }

    pub fn get_function_by_name(&self, name: &'mir str) -> Option<&MirFunction<'mir>> {
        self.functions.get(self.function_names_reverse.get(name)?)
    }

    /// Get the function id for the given name.
    pub fn get_function_id(&self, name: &'mir str) -> Option<MirFunctionRef> {
        self.function_names_reverse.get(name).copied()
    }

    /// Get the function name for the given id.
    pub fn get_function_name(&self, id: MirFunctionRef) -> Option<&'mir str> {
        self.function_names.get(&id).copied()
    }

    /// Get the function type for the given id.
    pub fn get_function_type(&self, id: MirFunctionRef) -> Option<&'mir MirFunctionType<'mir>> {
        self.function_types.get(&id).copied()
    }
}

pub struct MirModuleContext<'mir, 'hir> {
    cc: &'mir CompileContext<'mir>,
    hir_module: &'hir HirModule<'hir>,
    data: MirModuleData<'mir>,
    function_id: usize,
}

impl<'mir, 'hir> MirModuleContext<'mir, 'hir> {
    pub fn new(cc: &'mir CompileContext<'mir>, hir_module: &'hir HirModule<'hir>) -> Self {
        Self {
            cc,
            hir_module,
            function_id: 0,
            data: MirModuleData::default(),
        }
    }

    pub fn build(self) -> MirModule<'mir> {
        MirModule::new(self.data)
    }

    /// Reserve the next function id.
    pub fn forward_declare_function(
        &mut self,
        name: &str,
        ty: &'mir MirFunctionType<'mir>,
    ) -> MirFunctionRef {
        let name = self.cc.intern_str(name);
        let id = MirFunctionRef::new(self.function_id);
        self.function_id += 1;
        self.data.function_names.insert(id, name);
        self.data.function_types.insert(id, ty);
        self.data.function_names_reverse.insert(name, id);
        id
    }

    pub fn data(&self) -> &MirModuleData<'mir> {
        &self.data
    }

    /// Provide the completed MIR function.
    pub fn implement_function(&mut self, id: MirFunctionRef, fun: MirFunction<'mir>) {
        if self.data.functions.contains_key(&id) {
            ice!("function already implemented");
        }
        self.data.functions.insert(id, fun);
    }
}
