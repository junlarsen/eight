use crate::ty::{HirBooleanTy, HirFunctionTy, HirInteger32Ty, HirMetaTy, HirNominalTy, HirPointerTy, HirTy, HirTyId, HirUninitializedTy, HirUnitTy, HirVariableTy};
use bumpalo::Bump;
use eight_span::Span;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::rc::Rc;

/// An arena allocator for Hir nodes.
///
/// For memory efficiency, we intern a number of nodes in the Hir.
///
/// It also simplifies comparison of types to pointer equality.
pub struct HirArena<'arena> {
    allocator: Rc<Bump>,
    type_arena: TypeArena<'arena>,
    name_arena: HirNameArena<'arena>,
    phantom: PhantomData<&'arena ()>,
}

impl<'arena> Default for HirArena<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'arena> HirArena<'arena> {
    pub fn new() -> Self {
        let allocator = Rc::new(Bump::new());
        Self {
            type_arena: TypeArena::new(allocator.clone()),
            name_arena: HirNameArena::new(allocator.clone()),
            allocator: allocator.clone(),
            phantom: PhantomData,
        }
    }

    /// Intern an arbitrary value.
    pub fn intern<T>(&'arena self, v: T) -> &'arena mut T {
        self.allocator.alloc(v)
    }

    /// Get a reference to the type interning arena.
    pub fn types(&'arena self) -> &'arena TypeArena<'arena> {
        &self.type_arena
    }

    /// Get a reference to the name interning arena.
    pub fn names(&'arena self) -> &'arena HirNameArena<'arena> {
        &self.name_arena
    }
}

/// An arena for interning HIR names.
///
/// This is a general purpose string interning arena.
pub struct HirNameArena<'arena> {
    allocator: Rc<Bump>,
    intern: RefCell<HashSet<&'arena str>>,
}

impl<'arena> HirNameArena<'arena> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashSet::new()),
        }
    }

    pub fn get(&'arena self, name: &str) -> &'arena str {
        if let Some(interned) = self.intern.borrow().get(name) {
            return interned;
        }
        let id = self.allocator.alloc_str(name);
        self.intern.borrow_mut().insert(id);
        id
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
    allocator: Rc<Bump>,
    intern: RefCell<HashMap<HirTyId, &'arena HirTy<'arena>>>,
}

impl<'arena> TypeArena<'arena> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashMap::new()),
        }
    }

    /// Get a type from the arena.
    pub fn get_type(&'arena self, id: HirTyId) -> Option<&'arena HirTy> {
        self.intern.borrow().get(&id).copied()
    }

    pub fn get_pointer_ty(&'arena self, ty: &'arena HirTy) -> &'arena HirTy {
        let id = HirTyId::compute_pointer_ty_id(&HirTyId::from(ty));
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Pointer(HirPointerTy { inner: ty }))
        })
    }

    pub fn get_nominal_ty(&'arena self, name: &'arena str, name_span: Span) -> &'arena HirTy {
        let id = HirTyId::compute_nominal_ty_id(name);
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Nominal(HirNominalTy { name, name_span }))
        })
    }

    pub fn get_integer32_ty(&'arena self) -> &'arena HirTy {
        let id = HirTyId::compute_integer32_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Integer32(HirInteger32Ty {})))
    }

    pub fn get_boolean_ty(&'arena self) -> &'arena HirTy {
        let id = HirTyId::compute_boolean_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Boolean(HirBooleanTy {})))
    }

    pub fn get_unit_ty(&'arena self) -> &'arena HirTy {
        let id = HirTyId::compute_unit_ty_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(HirTy::Unit(HirUnitTy {})))
    }

    pub fn get_uninitialized_ty(&'arena self) -> &'arena HirTy {
        let id = HirTyId::compute_uninitialized_ty_id();
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Uninitialized(HirUninitializedTy {}))
        })
    }

    pub fn get_variable_ty(&'arena self, depth: u32, index: u32) -> &'arena HirTy {
        let id = HirTyId::compute_variable_ty_id(depth, index);
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(HirTy::Variable(HirVariableTy { depth, index }))
        })
    }

    pub fn get_function_ty(
        &'arena self,
        return_type: &'arena HirTy,
        parameters: Vec<&'arena HirTy>,
    ) -> &'arena HirTy {
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
    
    pub fn get_meta_ty(&'arena self, index: u32) -> &'arena HirTy<'arena> {
        let id = HirTyId::compute_meta_ty_id();
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator.alloc(HirTy::Meta(HirMetaTy { index }))
        })
    }
}
