use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::HashMap;
use crate::HirName;
use crate::ty::{HirBooleanTy, HirFunctionTy, HirInteger32Ty, HirNominalTy, HirPointerTy, HirTy, HirTyId, HirUninitializedTy, HirUnitTy, HirVariableTy};

/// A type arena for Hir types.
///
/// In order to avoid duplication of types, we use an arena allocator to allocate the types. This
/// arena acts as a cache for the types, meaning we can look up types from the arena by their ID
/// or characteristics.
///
/// It also simplifies comparison of types to pointer equality.
#[derive(Debug)]
pub struct HirArena<'a> {
    arena: &'a Bump,
    type_store: RefCell<HashMap<HirTyId, &'a HirTy<'a>>>,
}

impl<'arena> HirArena<'arena> {
    pub fn new(bump: &'arena Bump) -> Self {
        Self {
            arena: bump,
            type_store: RefCell::new(HashMap::new()),
        }
    }

    /// Get a type from the arena.
    pub fn get_type(&self, id: HirTyId) -> Option<&HirTy> {
        self.type_store.borrow().get(&id).copied()
    }

    pub fn get_pointer_ty(&self, ty: &'arena HirTy) -> &HirTy {
        let id = HirTyId::compute_pointer_ty_id(&HirTyId::from(ty));
        self.type_store
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.arena.alloc(HirTy::Pointer(HirPointerTy { inner: ty })))
    }

    pub fn get_nominal_ty(&self, name: &HirName) -> &HirTy {
        let id = HirTyId::compute_nominal_ty_id(name.name.as_str());
        self.type_store.borrow_mut().entry(id).or_insert_with(|| {
            self.arena
                .alloc(HirTy::Nominal(HirNominalTy { name: name.clone() }))
        })
    }

    pub fn get_integer32_ty(&self) -> &HirTy {
        let id = HirTyId::compute_integer32_ty_id();
        self.type_store
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.arena.alloc(HirTy::Integer32(HirInteger32Ty {})))
    }

    pub fn get_boolean_ty(&self) -> &HirTy {
        let id = HirTyId::compute_boolean_ty_id();
        self.type_store
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.arena.alloc(HirTy::Boolean(HirBooleanTy {})))
    }

    pub fn get_unit_ty(&self) -> &HirTy {
        let id = HirTyId::compute_unit_ty_id();
        self.type_store
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.arena.alloc(HirTy::Unit(HirUnitTy {})))
    }

    pub fn get_uninitialized_ty(&self) -> &HirTy {
        let id = HirTyId::compute_uninitialized_ty_id();
        self.type_store.borrow_mut().entry(id).or_insert_with(|| {
            self.arena
                .alloc(HirTy::Uninitialized(HirUninitializedTy {}))
        })
    }

    pub fn get_variable_ty(&self, var: usize) -> &HirTy {
        let id = HirTyId::compute_variable_ty_id(var);
        self.type_store
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.arena.alloc(HirTy::Variable(HirVariableTy { var })))
    }

    pub fn get_function_ty(
        &self,
        return_type: &'arena HirTy,
        parameters: Vec<&'arena HirTy>,
    ) -> &HirTy {
        let parameter_ids = parameters
            .iter()
            .map(|p| HirTyId::from(*p))
            .collect::<Vec<_>>();
        let return_type_id = HirTyId::from(return_type);
        let id = HirTyId::compute_function_ty_id(&return_type_id, parameter_ids.as_slice());
        self.type_store.borrow_mut().entry(id).or_insert_with(|| {
            self.arena.alloc(HirTy::Function(HirFunctionTy {
                return_type,
                parameters,
            }))
        })
    }
}