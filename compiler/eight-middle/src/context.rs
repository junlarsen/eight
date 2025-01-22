use crate::hir::ty::{
    HirBooleanTy, HirFunctionTy, HirInteger32Ty, HirMetaTy, HirNominalTy, HirPointerTy, HirTy,
    HirTyId, HirUninitializedTy, HirUnitTy, HirVariableTy,
};
use crate::intern::{StringInterner, TypedInterner};
use crate::mir::ty::{
    MirBoolType, MirFunctionType, MirInteger32Type, MirPointerType, MirType, MirTypeId, MirVoidType,
};
use bumpalo::Bump;
use eight_span::Span;
use std::rc::Rc;

/// A shared context for the middle-end and backend components.
pub struct CompileContext<'be> {
    allocator: Rc<Bump>,
    strings: StringInterner<'be>,
    mir_types: TypedInterner<'be, MirTypeId, MirType<'be>>,
    hir_types: TypedInterner<'be, HirTyId, HirTy<'be>>,
}

impl<'be> Default for CompileContext<'be> {
    fn default() -> Self {
        let alloc = Rc::new(Bump::new());
        Self {
            allocator: Rc::new(Bump::new()),
            strings: StringInterner::new(alloc.clone()),
            mir_types: TypedInterner::new(alloc.clone()),
            hir_types: TypedInterner::new(alloc),
        }
    }
}

impl<'be> CompileContext<'be> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a value into the arena.
    ///
    /// This can be used to allocate things that should be dropped automatically when the compiler
    /// exits, and that are fine being non-owning references.
    pub fn arena_alloc<T>(&'be self, v: T) -> &'be T {
        self.allocator.alloc(v)
    }

    /// Intern a string into the context.
    pub fn intern_str<T: AsRef<str>>(&'be self, name: T) -> &'be str {
        self.strings.get(name.as_ref())
    }

    /// Intern something that can be converted to a string into the context.
    pub fn intern_as_str<T: ToString>(&'be self, name: T) -> &'be str {
        self.intern_str(name.to_string())
    }
}

/// Implementation block for the HIR components.
impl<'be> CompileContext<'be> {
    pub fn hir_pointer_type(&'be self, ty: &'be HirTy) -> &'be HirTy {
        let id = HirTyId::compute_pointer_ty_id(&HirTyId::from(ty));
        self.hir_types
            .get_interned(id, HirTy::Pointer(HirPointerTy { inner: ty }))
    }

    pub fn hir_nominal_type(&'be self, name: &'be str, name_span: Span) -> &'be HirTy {
        let id = HirTyId::compute_nominal_ty_id(name);
        self.hir_types
            .get_interned(id, HirTy::Nominal(HirNominalTy { name, name_span }))
    }

    pub fn hir_integer32_type(&'be self) -> &'be HirTy {
        let id = HirTyId::compute_integer32_ty_id();
        self.hir_types
            .get_interned(id, HirTy::Integer32(HirInteger32Ty {}))
    }

    pub fn hir_boolean_type(&'be self) -> &'be HirTy {
        let id = HirTyId::compute_boolean_ty_id();
        self.hir_types
            .get_interned(id, HirTy::Boolean(HirBooleanTy {}))
    }

    pub fn hir_unit_type(&'be self) -> &'be HirTy {
        let id = HirTyId::compute_unit_ty_id();
        self.hir_types.get_interned(id, HirTy::Unit(HirUnitTy {}))
    }

    pub fn hir_uninitialized_type(&'be self) -> &'be HirTy {
        let id = HirTyId::compute_uninitialized_ty_id();
        self.hir_types
            .get_interned(id, HirTy::Uninitialized(HirUninitializedTy {}))
    }

    pub fn hir_variable_type(&'be self, depth: u32, index: u32) -> &'be HirTy {
        let id = HirTyId::compute_variable_ty_id(depth, index);
        self.hir_types
            .get_interned(id, HirTy::Variable(HirVariableTy { depth, index }))
    }

    pub fn hir_function_type(
        &'be self,
        return_type: &'be HirTy,
        parameters: Vec<&'be HirTy>,
    ) -> &'be HirTy {
        let parameter_ids = parameters
            .iter()
            .map(|p| HirTyId::from(*p))
            .collect::<Vec<_>>();
        let return_type_id = HirTyId::from(return_type);
        let id = HirTyId::compute_function_ty_id(&return_type_id, parameter_ids.as_slice());
        self.hir_types.get_interned(
            id,
            HirTy::Function(HirFunctionTy {
                return_type,
                parameters,
            }),
        )
    }

    pub fn hir_meta_type(&'be self, index: u32) -> &'be HirTy<'be> {
        let id = HirTyId::compute_meta_ty_id(index);
        self.hir_types
            .get_interned(id, HirTy::Meta(HirMetaTy { index }))
    }
}

impl<'be> CompileContext<'be> {
    pub fn mir_i32_type(&'be self) -> &'be MirType {
        let id = MirTypeId::compute_i32_type_id();
        self.mir_types
            .get_interned(id, MirType::Integer32(MirInteger32Type))
    }

    pub fn mir_bool_type(&'be self) -> &'be MirType {
        let id = MirTypeId::compute_bool_type_id();
        self.mir_types.get_interned(id, MirType::Bool(MirBoolType))
    }

    pub fn mir_void_type(&'be self) -> &'be MirType {
        let id = MirTypeId::compute_void_type_id();
        self.mir_types.get_interned(id, MirType::Void(MirVoidType))
    }

    pub fn mir_pointer_type(&'be self, inner: &'be MirType<'be>) -> &'be MirType {
        let inner_id = MirTypeId::from(inner);
        let id = MirTypeId::compute_pointer_type_id(&inner_id);
        self.mir_types
            .get_interned(id, MirType::Pointer(MirPointerType { inner }))
    }

    pub fn mir_function_type(
        &'be self,
        return_type: &'be MirType,
        parameters: Vec<&'be MirType>,
    ) -> &'be MirType<'be> {
        let return_type_id = MirTypeId::from(return_type);
        let parameters_ids = parameters
            .iter()
            .map(|ty| MirTypeId::from(*ty))
            .collect::<Vec<_>>();
        let id = MirTypeId::compute_function_type_id(&return_type_id, parameters_ids.as_slice());
        self.mir_types.get_interned(
            id,
            MirType::Function(MirFunctionType {
                return_type,
                parameters,
            }),
        )
    }
}
