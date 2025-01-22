use bumpalo::Bump;
use eight_middle::intern::StringInterner;
use eight_middle::mir::ty::{
    MirBoolType, MirFunctionType, MirInteger32Type, MirPointerType, MirType, MirTypeId, MirVoidType,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// An arena allocator and interner for the MIR.
///
/// This type can be considered analogous to the LLVMContext type in LLVM.
pub struct MirArena<'arena> {
    allocator: Rc<Bump>,
    name_arena: StringInterner<'arena>,
    type_arena: MirTypeArena<'arena>,
}

impl<'arena> Default for MirArena<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'arena> MirArena<'arena> {
    pub fn new() -> Self {
        let allocator = Rc::new(Bump::new());
        Self {
            name_arena: StringInterner::new(allocator.clone()),
            type_arena: MirTypeArena::new(allocator.clone()),
            allocator,
        }
    }

    pub fn names(&'arena self) -> &'arena StringInterner<'arena> {
        &self.name_arena
    }

    pub fn types(&'arena self) -> &'arena MirTypeArena<'arena> {
        &self.type_arena
    }
}

/// An arena and interner for MIR types.
pub struct MirTypeArena<'arena> {
    allocator: Rc<Bump>,
    intern: RefCell<HashMap<MirTypeId, &'arena MirType<'arena>>>,
}

impl<'arena> MirTypeArena<'arena> {
    pub fn new(allocator: Rc<Bump>) -> Self {
        Self {
            allocator,
            intern: RefCell::new(HashMap::new()),
        }
    }

    /// Get the MIR integer type.
    pub fn get_i32_type(&'arena self) -> &'arena MirType {
        let id = MirTypeId::compute_i32_type_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(&MirType::Integer32(MirInteger32Type)))
    }

    /// Get the MIR boolean type.
    pub fn get_bool_type(&'arena self) -> &'arena MirType {
        let id = MirTypeId::compute_bool_type_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(&MirType::Bool(MirBoolType)))
    }

    /// Get the MIR void type.
    pub fn get_void_type(&'arena self) -> &'arena MirType {
        let id = MirTypeId::compute_void_type_id();
        self.intern
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| self.allocator.alloc(MirType::Void(MirVoidType)))
    }

    /// Get the MIR opaque pointer type.
    pub fn get_pointer_type(&'arena self, inner: &'arena MirType<'arena>) -> &'arena MirType {
        let inner_id = MirTypeId::from(inner);
        let id = MirTypeId::compute_pointer_type_id(&inner_id);
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator
                .alloc(MirType::Pointer(MirPointerType { inner }))
        })
    }

    /// Get a MIR function type.
    ///
    /// This type is not used to represent anything but the signature of a HirFunction.
    pub fn get_function_type(
        &'arena self,
        return_type: &'arena MirType,
        parameters: Vec<&'arena MirType>,
    ) -> &'arena MirType {
        let return_type_id = MirTypeId::from(return_type);
        let parameters_ids = parameters
            .iter()
            .map(|ty| MirTypeId::from(*ty))
            .collect::<Vec<_>>();
        let id = MirTypeId::compute_function_type_id(&return_type_id, parameters_ids.as_slice());
        self.intern.borrow_mut().entry(id).or_insert_with(|| {
            self.allocator.alloc(MirType::Function(MirFunctionType {
                return_type,
                parameters,
            }))
        })
    }
}
