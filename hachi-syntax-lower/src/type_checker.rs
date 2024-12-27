//! The type checker for the syntax lowering pass.
//!
//! The type checker maintains a type environment that maps all syntax nodes to their types. It is
//! responsible for inferring the types of expressions, and for ensuring that the types of all
//! expressions match.
//!
//! The type system is a hindley-milner based type system.

use crate::error::{InvalidTypeReferenceError, TypeError, TypeResult};
use crate::scope::TypeEnvironment;
use crate::ty::Ty;
use hachi_syntax::{FunctionItem, Item, Span, TranslationUnit, Type, TypeItem, TypeMemberItem};
use std::collections::HashMap;

pub struct TypeChecker {
    scope: TypeEnvironment<Ty>,
    type_ids: usize,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            scope: TypeEnvironment::new(),
            type_ids: 0,
        }
    }

    /// Get a new type variable.
    ///
    /// This type has zero constraints at the moment, and is unbound to any other type.
    pub fn get_unique_type_variable(&mut self) -> Ty {
        self.type_ids += 1;
        Ty::TVariable(self.type_ids)
    }

    pub fn get_unique_type_id(&mut self) -> usize {
        self.type_ids += 1;
        self.type_ids
    }

    /// Apply the `Var` rule to the given type.
    ///
    /// If the given term exists in the current type environment, return its type. Otherwise, we are
    /// trying to reference a type that does not exist.
    pub fn var(&self, x: &str, location: &Span) -> TypeResult<&Ty> {
        let ty = self.scope.find(x).ok_or(TypeError::InvalidTypeReference(
            InvalidTypeReferenceError {
                span: location.clone(),
                name: x.to_owned(),
            },
        ))?;
        Ok(ty)
    }
}

impl TypeChecker {
    /// Traverse a TranslationUnit and infer the types of all its items.
    ///
    /// The type checker will hoist the declarations of all types and functions into the top-level
    /// scope before each item is visited.
    ///
    /// This enables us to perform mutual recursion between two functions, as the type checker will
    /// understand that both functions exist even though they are defined one after another.
    pub fn visit_translation_unit(&mut self, node: &TranslationUnit) -> TypeResult<()> {
        self.scope.enter_scope();
        // Hoist all the types and functions into the top-level scope
        for item in &node.items {
            let (name, ty) = match item.as_ref() {
                // Functions are inserted as unnamed TConstructors into the scope.
                Item::Function(f) => {
                    let type_parameters = f
                        .type_parameters
                        .iter()
                        .map(|p| (&p.name.name, self.get_unique_type_id()))
                        .collect::<HashMap<_, _>>();
                    // Resolve the types of all the parameters. We check if the type is referring to
                    // a type parameter, and if so, we replace it with the type variables that we
                    // just created.
                    let parameters = f
                        .parameters
                        .iter()
                        .map(|p| {
                            let name = &p.name.name;
                            if let Some(type_id) = type_parameters.get(name) {
                                return Box::new(Ty::TVariable(*type_id));
                            }
                            Box::new(p.r#type.as_ref().into())
                        })
                        .collect();
                    let return_type = match &f.return_type {
                        Some(t) => t.as_ref().into(),
                        None => Ty::TConst("void".to_owned()),
                    };
                    let ty = Ty::TConstructor(Box::new(return_type), parameters);
                    (&f.name, ty)
                }
                Item::IntrinsicFunction(f) => {
                    let type_parameters = f
                        .type_parameters
                        .iter()
                        .map(|p| (&p.name.name, self.get_unique_type_id()))
                        .collect::<HashMap<_, _>>();
                    // Resolve the types of all the parameters. We check if the type is referring to
                    // a type parameter, and if so, we replace it with the type variables that we
                    // just created.
                    let parameters = f
                        .parameters
                        .iter()
                        .map(|p| {
                            let name = &p.name.name;
                            if let Some(type_id) = type_parameters.get(name) {
                                return Box::new(Ty::TVariable(*type_id));
                            }
                            Box::new(p.r#type.as_ref().into())
                        })
                        .collect();
                    let return_type = f.return_type.as_ref().into();
                    let ty = Ty::TConstructor(Box::new(return_type), parameters);
                    (&f.name, ty)
                }
                // Types are not generic at the moment, so we can just use the name of the type.
                // When we add generic types, we will need to introduce a TConstructor here instead.
                Item::Type(t) => {
                    let ty = Ty::TConst(t.name.name.clone());
                    (&t.name, ty)
                }
                Item::IntrinsicType(t) => {
                    let ty = Ty::TConst(t.name.name.clone());
                    (&t.name, ty)
                }
            };
            self.scope.add(&name.name, ty);
        }

        // Traverse through all the items in the translation unit
        for item in &node.items {
            self.visit_item(item)?;
        }
        self.scope.leave_scope();

        Ok(())
    }

    /// Visit an item.
    pub fn visit_item(&mut self, node: &Item) -> TypeResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(f),
            Item::Type(t) => self.visit_type_item(t),
            Item::IntrinsicFunction(_) => Ok(()),
            Item::IntrinsicType(_) => Ok(()),
        }
    }

    /// Visit a function item.
    pub fn visit_function_item(&mut self, node: &FunctionItem) -> TypeResult<()> {
        Ok(())
    }

    /// Visit a type item.
    ///
    /// This function ensures that all members of the type are defined.
    pub fn visit_type_item(&mut self, node: &TypeItem) -> TypeResult<()> {
        for member in &node.members {
            self.visit_type_member(member)?;
        }
        Ok(())
    }

    /// Visit a type member.
    ///
    /// This function ensures that the type of the member is defined.
    fn visit_type_member(&mut self, node: &TypeMemberItem) -> TypeResult<()> {
        self.visit_type(&node.r#type)?;
        Ok(())
    }

    /// Visit a type.
    ///
    /// This function ensures that the type is defined in the current scope.
    fn visit_type(&mut self, node: &Type) -> TypeResult<()> {
        match node {
            Type::Named(t) => {
                self.var(&t.name.name, &t.name.span)?;
            }
            Type::Pointer(t) => self.visit_type(&t.inner)?,
            Type::Reference(t) => self.visit_type(&t.inner)?,
            Type::Boolean(_) => {
                self.var("bool", &node.span())?;
            }
            Type::Integer32(_) => {
                self.var("i32", &node.span())?;
            }
            Type::Unit(_) => {
                self.var("void", &node.span())?;
            }
        };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::error::{InvalidTypeReferenceError, TypeError, TypeResult};
    use crate::type_checker::TypeChecker;
    use hachi_macros::{assert_err, assert_ok};

    fn assert_type_check(input: &str) -> TypeResult<()> {
        let mut checker = TypeChecker::new();
        let mut lexer = hachi_syntax::Lexer::new(input);
        let mut parser = hachi_syntax::Parser::new(&mut lexer);
        let tu = parser.parse().expect("failed to parse translation unit");
        checker.visit_translation_unit(&tu)
    }

    #[test]
    fn test_forward_declaration_of_items() {
        assert_ok!(assert_type_check(
            r#"
        intrinsic_type i32;
        fn uses_foo(x: Foo) -> Foo {}
        type Foo = { elem: i32, }
        "#
        ));
        assert_ok!(assert_type_check(
            r#"
        intrinsic_type i32;
        fn mutually() -> i32 {
          return recursive();
        }
        fn recursive() -> i32 {
           return mutually();
        }
        "#
        ));
    }

    #[test]
    fn test_intrinsic_types_are_forward_declared() {
        assert_ok!(assert_type_check(
            r#"
        fn consumes_i32(x: i32) {}
        intrinsic_type i32;
        "#
        ));
    }

    #[test]
    fn test_invalid_type_reference_fails_type_check() {
        let err = assert_err!(assert_type_check(
            r#"
        type Coordinate = { p: Point, }
        "#
        ));
        assert!(
            matches!(err, TypeError::InvalidTypeReference(InvalidTypeReferenceError {
            name,
            ..
        }) if name == "Point")
        );
    }

    #[test]
    fn test_type_parameters_are_substituted_in_fn() {
        assert_ok!(assert_type_check(
            r#"
        fn foo<T>(x: T) -> T {}
        "#
        ));
    }
}
