use crate::ty::{
    HirBooleanTy, HirFunctionTy, HirInteger32Ty, HirNominalTy, HirPointerTy, HirTy, HirTyId,
    HirUninitializedTy, HirUnitTy, HirVariableTy,
};
use crate::HirName;
use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::HashMap;

/// An arena allocator for Hir nodes.
///
/// For memory efficiency, we intern a number of nodes in the Hir.
///
/// It also simplifies comparison of types to pointer equality.
pub struct HirArena<'arena> {
    allocator: &'arena Bump,
    type_arena: TypeArena<'arena>,
}

impl<'arena> HirArena<'arena> {
    pub fn new(bump: &'arena Bump) -> Self {
        Self {
            allocator: bump,
            type_arena: TypeArena::new(bump),
        }
    }

    pub fn intern<T>(&self, v: T) -> &'arena mut T {
        self.allocator.alloc(v)
    }

    pub fn types(&self) -> &TypeArena<'arena> {
        &self.type_arena
    }
}

/// An arena and interner for the HIR types.
///
/// Because types are duplicated in a lot of nodes (for example, all Expr nodes have a type), we
/// want to save memory by interning the types instead.
///
/// This uses a RefCell because we don't want to impose a mutable borrow on the arena when getting
/// types from the interner.
///
/// This is safe because each type is only ever produced once by the interner, so two mutable
/// borrows of the RefCell is never possible.
pub struct TypeArena<'arena> {
    allocator: &'arena Bump,
    intern: RefCell<HashMap<HirTyId, &'arena HirTy<'arena>>>,
}

impl<'arena> TypeArena<'arena> {
    pub fn new(bump: &'arena Bump) -> Self {
        Self {
            allocator: bump,
            intern: RefCell::new(HashMap::new()),
        }
    }

    /// Get a type from the arena.
    pub fn get_type(&self, id: HirTyId) -> Option<&HirTy> {
        self.intern.borrow().get(&id).copied()
    }

    pub fn get_pointer_ty(&self, ty: &'arena HirTy) -> &HirTy {
        let id = HirTyId::compute_pointer_ty_id(&HirTyId::from(ty));
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Pointer(HirPointerTy { inner: ty }))
        })
    }

    pub fn get_nominal_ty(&self, name: &HirName) -> &HirTy {
        let id = HirTyId::compute_nominal_ty_id(name.name.as_str());
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Nominal(HirNominalTy { name: name.clone() }))
        })
    }

    pub fn get_integer32_ty(&self) -> &HirTy {
        let id = HirTyId::compute_integer32_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Integer32(HirInteger32Ty {})))
    }

    pub fn get_boolean_ty(&self) -> &HirTy {
        let id = HirTyId::compute_boolean_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Boolean(HirBooleanTy {})))
    }

    pub fn get_unit_ty(&self) -> &HirTy {
        let id = HirTyId::compute_unit_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Unit(HirUnitTy {})))
    }

    pub fn get_uninitialized_ty(&self) -> &HirTy {
        let id = HirTyId::compute_uninitialized_ty_id();
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Uninitialized(HirUninitializedTy {}))
        })
    }

    pub fn get_variable_ty(&self, depth: u32, index: u32) -> &HirTy {
        let id = HirTyId::compute_variable_ty_id(depth, index);
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Variable(HirVariableTy { depth, index }))
        })
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
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator.alloc(HirTy::Function(HirFunctionTy {
                return_type,
                parameters,
            }))
        })
    }
}
