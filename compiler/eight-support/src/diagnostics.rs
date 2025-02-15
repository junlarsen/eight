use crate::span::Span;
use miette::Diagnostic;
use thiserror::Error;

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

#[derive(Error, Diagnostic, Debug, PartialEq)]
#[diagnostic(code(sema::trait_method_does_not_exist))]
#[error("trait {trait_name} does not have method {method_name}")]
pub struct TraitMethodDoesNotExistError {
    pub trait_name: String,
    pub method_name: String,
    #[label = "required method {method_name} for trait {trait_name}"]
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

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::duplicate_type_parameter))]
#[error("type parameter with name {name} has already been defined for this item")]
pub struct DuplicateTypeParameterError {
    pub name: String,
    #[label = "previous declared here"]
    pub previous: Span,
    #[label = "the type parameter {name} shadows an existing type with the same name"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(sema::duplicate_let_binding_in_scope),
    help("give this binding a different name")
)]
#[error("binding {name} has already been declared in this scope")]
pub struct DuplicateLetBindingInSameScopeError {
    pub name: String,
    #[label = "previously declared here"]
    pub previous: Span,
    #[label = "the binding {name} shadows an existing binding with the same name"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::constructing_non_struct_type))]
#[error("cannot construct a non-struct type")]
pub struct ConstructingNonStructTypeError {
    pub name: String,
    #[label = "the type {name} is not a struct type"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(sema::constructing_pointer_type),
    help("did you mean to construct the inner type?")
)]
#[error("cannot construct a pointer type")]
pub struct ConstructingPointerTypeError {
    pub name: String,
    #[label = "type {name} is a pointer type and cannot be constructed"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::wrong_function_type_argument_count))]
#[error("function {name} requires {expected} type arguments, but {actual} were supplied")]
pub struct WrongFunctionTypeArgumentCount {
    pub expected: usize,
    pub actual: usize,
    pub name: String,
    #[label = "supplied {actual} type arguments"]
    pub span: Span,
    #[label = "declares {expected} type arguments"]
    pub function_declaration_loc: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(sema::dereference_of_non_pointer))]
#[error("type {ty} is not a pointer type, and cannot be dereferenced")]
pub struct DereferenceOfNonPointerError {
    pub ty: String,
    #[label = "{ty} is not dereferenceable"]
    pub span: Span,
}

/// Signals that the parser has reached the end of the input stream.
///
/// This error is only emitted to the diagnostic engine when the parser produces it. See the note
/// on [`Lexer::next`] for more information about how the parser handles this error once it is
/// emitted from the lexer.
///
/// It should also be noted that both lexer and parser produce this error in their signatures, but
/// as mentioned, only the parser emits it to the diagnostic engine.
#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(syntax::unexpected_end_of_file),
    help("add more input to form a valid program")
)]
#[error("expected more characters after this")]
pub struct UnexpectedEndOfFileError {
    #[label = "required more input to parse"]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug, PartialEq)]
#[diagnostic(
    code(syntax::unfinished_token),
    help("did you forget to add a '{expected}' character here?")
)]
#[error("expected another '{expected}' character here")]
pub struct UnfinishedTokenError {
    pub expected: char,
    #[label = "this alone does not form a valid token"]
    pub span: Span,
}

const MAX_INTEGER_32_VALUE: i32 = i32::MAX;

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(
    code(syntax::invalid_integer_literal),
    help("did you mean to specify a larger integer type?")
)]
#[error("found illegal i32 literal")]
pub struct InvalidIntegerLiteralError {
    pub buf: String,
    #[label("the maximum value that can be represented by an i32 is {MAX_INTEGER_32_VALUE}")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_character))]
#[error("found illegal character during parsing")]
pub struct UnexpectedCharacterError {
    pub ch: char,
    #[label("the character '{ch}' does not parse into any tokens")]
    pub span: Span,
}

#[derive(Error, Diagnostic, Debug)]
#[diagnostic(code(syntax::unexpected_token))]
#[error("found unexpected token during parsing")]
pub struct UnexpectedTokenError {
    pub token: String,
    #[label("was not expecting to find '{token}' in this position")]
    pub span: Span,
}
