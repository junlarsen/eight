use eight_macros::declare_error_type;
use eight_span::Span;
use miette::Diagnostic;
use thiserror::Error;

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
        TraitMissingInstance(TraitMissingInstanceError),
        WrongTraitTypeArgumentCount(WrongTraitTypeArgumentCount),
    }
}

/// Handy type alias for all HIR-related errors.
pub type HirResult<T> = Result<T, HirError>;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::unknown_type))]
#[error("{name} does not name a known type")]
pub struct UnknownTypeError {
    pub name: String,
    #[label = "could not find type {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_reference))]
#[error("invalid reference to {name}")]
pub struct InvalidReferenceError {
    pub name: String,
    #[label = "no value in scope named {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::infinitely_recursive_type))]
#[error("type is recursive")]
pub struct TypeFieldInfiniteRecursionError {
    pub type_name: String,
    pub offending_field: String,
    #[label = "type {type_name} has an infinite recursion in field {offending_field}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::break_outside_loop))]
#[error("break statement outside of loop")]
pub struct BreakOutsideLoopError {
    #[label = "there is no enclosing loop"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::continue_outside_loop))]
#[error("continue statement outside of loop")]
pub struct ContinueOutsideLoopError {
    #[label = "there is no enclosing loop"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::type_mismatch))]
#[error("type mismatch")]
pub struct TypeMismatchError {
    pub actual_type: String,
    pub expected_type: String,
    #[label = "the expression has type {actual_type}"]
    pub actual_loc: Span,
    #[label = "expected type {expected_type}"]
    pub expected_loc: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::function_type_mismatch))]
#[error("function types do not take the same number of arguments")]
pub struct FunctionTypeMismatchError {
    pub expected_ty: String,
    #[label = "the function has type {expected_ty}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::self_referential_type))]
#[error("type references itself")]
pub struct SelfReferentialTypeError {
    #[label = "this type refers to itself"]
    pub left: Span,
    #[label = "this type refers to itself"]
    pub right: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_struct_field_reference))]
#[error("invalid field reference to {name} in type {type_name}")]
pub struct InvalidStructFieldReferenceError {
    pub type_name: String,
    pub name: String,
    #[label = "unknown field {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::invalid_field_reference_of_non_struct))]
#[error("type {ty} is not a struct type and does not have fields")]
pub struct InvalidFieldReferenceOfNonStructError {
    pub ty: String,
    pub name: String,
    #[label = "unknown field {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::unknown_field))]
#[error("the type {type_name} does not have a field named {field_name}")]
pub struct UnknownFieldError {
    pub field_name: String,
    pub type_name: String,
    #[label = "this field does not exist"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::duplicate_field))]
#[error("the field {field_name} has already been provided")]
pub struct DuplicateFieldError {
    pub field_name: String,
    #[label = "this field does not exist"]
    pub span: Span,
    pub first_location: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::missing_field))]
#[error("the field {field_name} is missing in construction of {type_name}")]
pub struct MissingFieldError {
    pub type_name: String,
    pub field_name: String,
    #[label = "construction does not name field {field_name}"]
    pub span: Span,
    #[label = "field {field_name} defined here"]
    pub defined_at: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::unknown_intrinsic_type_type))]
#[error("unknown intrinsic type {name}")]
pub struct UnknownIntrinsicTypeError {
    pub name: String,
    #[label = "could not find type {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::trait_instance_missing_fn))]
#[error("trait instance {name} does not derive method {method}")]
pub struct TraitInstanceMissingFnError {
    pub name: String,
    pub method: String,
    #[label = "trait instance {name} does not derive method {method}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::trait_does_not_exist))]
#[error("trait {name} does not exist")]
pub struct TraitDoesNotExistError {
    pub name: String,
    #[label = "required trait {name} to exist"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::trait_missing_instance))]
#[error("trait {name} does not have instance {instance_name}")]
pub struct TraitMissingInstanceError {
    pub instance_name: String,
    pub name: String,
    #[label = "required instance {instance_name} for trait {name}"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::wrong_trait_type_argument_count))]
#[error("trait {name} requires {expected} type arguments, but {actual} were supplied")]
pub struct WrongTraitTypeArgumentCount {
    pub expected: usize,
    pub actual: usize,
    pub name: String,
    #[label = "supplied {actual} type arguments"]
    pub span: Span,
    #[label = "declares {expected} type arguments"]
    pub trait_declaration_loc: Span,
}
