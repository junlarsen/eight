pub mod hir {
    use crate::diagnostics::*;
    use eight_macros::declare_error_type;

    declare_error_type! {
        #[error("semantic error: {0}")]
        pub enum HirError {
            UnknownType(UnknownTypeError),
            InvalidReference(InvalidReferenceError),
            TypeFieldInfiniteRecursion(TypeFieldInfiniteRecursionError),
            BreakOutsideLoop(BreakOutsideLoopError),
            ContinueOutsideLoop(ContinueOutsideLoopError),
            TypeMismatch(TypeMismatchError),
            FunctionTypeMismatch(FunctionTypeMismatchError),
            SelfReferentialType(SelfReferentialTypeError),
            InvalidStructFieldReference(InvalidStructFieldReferenceError),
            InvalidFieldReferenceOfNonStruct(InvalidFieldReferenceOfNonStructError),
            UnknownField(UnknownFieldError),
            DuplicateField(DuplicateFieldError),
            MissingField(MissingFieldError),
            UnknownIntrinsicType(UnknownIntrinsicTypeError),
            TraitInstanceMissingFn(TraitInstanceMissingFnError),
            TraitDoesNotExist(TraitDoesNotExistError),
            TraitMethodDoesNotExist(TraitMethodDoesNotExistError),
            TraitMissingInstance(TraitMissingInstanceError),
            WrongTraitTypeArgumentCount(WrongTraitTypeArgumentCount),
            DuplicateTypeParameter(DuplicateTypeParameterError),
            DuplicateLetBindingInSameScope(DuplicateLetBindingInSameScopeError),
            ConstructingNonStructType(ConstructingNonStructTypeError),
            ConstructingPointerType(ConstructingPointerTypeError),
            WrongFunctionTypeArgumentCount(WrongFunctionTypeArgumentCount),
            DereferenceOfNonPointer(DereferenceOfNonPointerError),
        }
    }
}
