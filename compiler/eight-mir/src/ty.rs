use std::hash::{DefaultHasher, Hash, Hasher};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MirTypeId(u64);

impl MirTypeId {
    pub fn compute_i32_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x00.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_bool_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x01.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_void_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x02.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_pointer_type_id() -> Self {
        let mut hasher = DefaultHasher::new();
        0x03.hash(&mut hasher);
        Self(hasher.finish())
    }

    pub fn compute_function_type_id(return_type: &MirTypeId, parameters: &[MirTypeId]) -> Self {
        let mut hasher = DefaultHasher::new();
        (0x10, return_type, parameters).hash(&mut hasher);
        Self(hasher.finish())
    }
}

impl<'mir> From<&'mir MirType<'mir>> for MirTypeId {
    fn from(ty: &'mir MirType<'mir>) -> Self {
        match ty {
            MirType::Integer32(_) => MirTypeId::compute_i32_type_id(),
            MirType::Bool(_) => MirTypeId::compute_bool_type_id(),
            MirType::Void(_) => MirTypeId::compute_void_type_id(),
            MirType::Pointer(_) => MirTypeId::compute_pointer_type_id(),
            MirType::Function(ty) => {
                let parameters = ty
                    .parameters
                    .iter()
                    .map(|p| MirTypeId::from(*p))
                    .collect::<Vec<_>>();
                MirTypeId::compute_function_type_id(
                    &MirTypeId::from(ty.return_type),
                    parameters.as_slice(),
                )
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum MirType<'mir> {
    Integer32(MirInteger32Type),
    Bool(MirBoolType),
    Void(MirVoidType),
    /// A opaque pointer type.
    ///
    /// TODO: Is opaque pointers a good idea? LLVM does it, but maybe we can do better guided
    ///   optimizations if we know the inner type?
    Pointer(MirPointerType),
    Function(MirFunctionType<'mir>),
}

impl<'mir> MirType<'mir> {
    /// Get the size of the type in bytes.
    ///
    /// This is currently hard-coded for x86-64 and will need to be populated with target info once
    /// that has been added.
    pub fn get_size(&self) -> usize {
        match self {
            MirType::Integer32(_) => 32,
            MirType::Bool(_) => 1,
            MirType::Void(_) => 0,
            MirType::Pointer(_) => 64,
            MirType::Function(_) => unimplemented!(),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirInteger32Type;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirBoolType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirVoidType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirPointerType;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MirFunctionType<'mir> {
    pub return_type: &'mir MirType<'mir>,
    pub parameters: Vec<&'mir MirType<'mir>>,
}
