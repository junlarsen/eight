//! The type checker for the syntax lowering pass.
//!
//! The type checker maintains a type environment that maps all syntax nodes to their types. It is
//! responsible for inferring the types of expressions, and for ensuring that the types of all
//! expressions match.
//!
//! The type system is a hindley-milner based type system.

use crate::error::{InvalidTypeReferenceError, InvalidValueReferenceError, TypeError, TypeResult};
use crate::scope::TypeEnvironment;
use crate::ty::Ty;
use hachi_syntax::{
    BooleanLiteralExpr, Expr, ForStmt, FunctionItem, FunctionParameterItem, GroupExpr,
    IntegerLiteralExpr, IntrinsicFunctionItem, IntrinsicTypeItem, Item, LetStmt, ReferenceExpr,
    Span, Stmt, TranslationUnit, Type, TypeItem, TypeMemberItem,
};
use std::collections::{HashMap, VecDeque};

pub struct TypeChecker<'ast> {
    /// The hierarchical set of types available in the current scope.
    ///
    /// In practice, we don't actually support nested types, but when we have generic functions, the
    /// parameter types are local to that function. For this reason, we need the type context to act
    /// like a Deque.
    type_context: TypeEnvironment<Ty>,
    /// The hierarchical set of let bindings available in the current scope.
    ///
    /// We also bind functions into the [let_binding_context] as well. It makes sense to do so, even
    /// more so when we introduce lambdas/anonymous functions.
    let_binding_context: TypeEnvironment<Ty>,
    next_type_id: usize,

    /// Keep track of the current looping depth
    loop_depth: VecDeque<&'ast ForStmt>,
    /// Keep track of the current function depth
    ///
    /// The language does currently not support nested functions, so this VecDeque will always have
    /// a maximum length of 1 at the moment. This is just to unify with the implementation of the
    /// looping depth.
    function_depth: VecDeque<&'ast FunctionItem>,
}

impl<'ast> Default for TypeChecker<'ast> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'ast> TypeChecker<'ast> {
    pub fn new() -> Self {
        Self {
            type_context: TypeEnvironment::new(),
            let_binding_context: TypeEnvironment::new(),
            next_type_id: 0,
            loop_depth: VecDeque::new(),
            function_depth: VecDeque::new(),
        }
    }

    /// Get a new type variable.
    ///
    /// This type has zero constraints at the moment, and is unbound to any other type.
    pub fn fresh_type_variable(&mut self) -> Ty {
        Ty::TVariable(self.fresh_type_id())
    }

    /// Get a new type id.
    pub fn fresh_type_id(&mut self) -> usize {
        self.next_type_id += 1;
        self.next_type_id
    }

    /// Apply the `Var` rule to the given type.
    ///
    /// If the given term exists in the current type environment, return its type. Otherwise, we are
    /// trying to reference a type that does not exist.
    pub fn search_type(&self, x: &str, location: &Span) -> TypeResult<&Ty> {
        let ty = self
            .type_context
            .find(x)
            .ok_or(TypeError::InvalidTypeReference(InvalidTypeReferenceError {
                span: location.clone(),
                name: x.to_owned(),
            }))?;
        Ok(ty)
    }

    /// Get the given let-binding from the current scope.
    ///
    /// If the given term exists in the current let environment, return its type. Otherwise, we are
    /// trying to reference a value that does not exist.
    pub fn search_let_binding(&self, x: &str, location: &Span) -> TypeResult<&Ty> {
        let ty = self
            .let_binding_context
            .find(x)
            .ok_or(TypeError::InvalidValueReference(
                InvalidValueReferenceError {
                    span: location.clone(),
                    name: x.to_owned(),
                },
            ))?;
        Ok(ty)
    }

    pub fn unify(&self, a: &Ty, b: &Ty) -> TypeResult<()> {
        todo!()
    }
}

impl<'ast> TypeChecker<'ast> {
    /// Traverse a TranslationUnit and infer the types of all its items.
    ///
    /// The type checker will hoist the declarations of all types and functions into the top-level
    /// scope before each item is visited.
    ///
    /// This enables us to perform mutual recursion between two functions, as the type checker will
    /// understand that both functions exist even though they are defined one after another.
    pub fn visit_translation_unit(&mut self, node: &'ast TranslationUnit) -> TypeResult<()> {
        self.type_context.enter_scope();
        self.let_binding_context.enter_scope();
        // Hoist all the types and functions into the top-level scope
        for item in &node.items {
            match item.as_ref() {
                Item::Function(f) => self.insert_function_type(f)?,
                Item::IntrinsicFunction(f) => self.insert_intrinsic_function_type(f)?,
                Item::Type(t) => self.insert_type(t)?,
                Item::IntrinsicType(t) => self.insert_intrinsic_type(t)?,
            };
        }
        // Traverse through all the items in the translation unit
        for item in &node.items {
            self.visit_item(item)?;
        }
        self.let_binding_context.leave_scope();
        self.type_context.leave_scope();
        Ok(())
    }

    /// Insert a new function type into the type scope.
    fn insert_function_type(&mut self, item: &'ast FunctionItem) -> TypeResult<()> {
        let type_parameters = item
            .type_parameters
            .iter()
            .map(|p| (&p.name.name, self.fresh_type_id()))
            .collect::<HashMap<_, _>>();
        // Resolve the types of all the parameters. We check if the type is referring to
        // a type parameter, and if so, we replace it with the type variables that we
        // just created.
        let parameters = item
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
        let return_type = match &item.return_type {
            Some(t) => t.as_ref().into(),
            None => Ty::TConst("void".to_owned()),
        };
        let ty = Ty::TFunction(Box::new(return_type), parameters);
        self.let_binding_context.add(&item.name.name, ty);
        Ok(())
    }

    /// Insert a new intrinsic function type into the type scope.
    pub fn insert_intrinsic_function_type(
        &mut self,
        item: &'ast IntrinsicFunctionItem,
    ) -> TypeResult<()> {
        let type_parameters = item
            .type_parameters
            .iter()
            .map(|p| (&p.name.name, self.fresh_type_id()))
            .collect::<HashMap<_, _>>();
        // Resolve the types of all the parameters. We check if the type is referring to
        // a type parameter, and if so, we replace it with the type variables that we
        // just created.
        let parameters = item
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
        let return_type = item.return_type.as_ref().into();
        let ty = Ty::TFunction(Box::new(return_type), parameters);
        self.let_binding_context.add(&item.name.name, ty);
        Ok(())
    }

    /// Insert a new type into the type scope.
    pub fn insert_type(&mut self, item: &'ast TypeItem) -> TypeResult<()> {
        let mut fields = HashMap::new();
        for member in &item.members {
            let name = &member.name.name.clone();
            let ty = member.r#type.as_ref().into();
            fields.insert(name.clone(), Box::new(ty));
        }
        let ty = Ty::TRecord(fields);
        self.type_context.add(&item.name.name, ty);
        Ok(())
    }

    /// Insert a new intrinsic type into the type scope.
    ///
    /// Intrinsic types are (at the moment) all scalar types. This means that we can always assume
    /// that TConst is fine.
    pub fn insert_intrinsic_type(&mut self, item: &'ast IntrinsicTypeItem) -> TypeResult<()> {
        let ty = Ty::TConst(item.name.name.clone());
        self.type_context.add(&item.name.name, ty);
        Ok(())
    }

    /// Visit an item.
    pub fn visit_item(&mut self, node: &'ast Item) -> TypeResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(f),
            Item::Type(t) => self.visit_type_item(t),
            Item::IntrinsicFunction(_) => Ok(()),
            Item::IntrinsicType(_) => Ok(()),
        }
    }

    /// Visit a function item.
    ///
    /// In a function, we validate that all the types of the parameters are defined, that the
    /// return type is defined, and that the body of the function is well-typed.
    ///
    /// Any return statements are checked against the return type of the function.
    pub fn visit_function_item(&mut self, node: &'ast FunctionItem) -> TypeResult<()> {
        self.type_context.enter_scope();
        self.let_binding_context.enter_scope();
        // Insert all the type parameters into the scope
        for parameter in node.type_parameters.iter() {
            self.type_context
                .add(&parameter.name.name, self.fresh_type_variable());
        }

        // Ensure that all the parameter types are defined
        for parameter in &node.parameters {
            self.visit_function_parameter(parameter)?;
        }

        // If we have a return type, ensure that it is defined
        if let Some(return_type) = &node.return_type {
            self.visit_type(return_type)?;
        }

        // Validate the entire body of the function
        for statement in &node.body {
            self.visit_stmt(statement)?;
        }

        self.let_binding_context.leave_scope();
        self.type_context.leave_scope();
        Ok(())
    }

    /// Visit a function parameter.
    pub fn visit_function_parameter(
        &mut self,
        node: &'ast FunctionParameterItem,
    ) -> TypeResult<()> {
        self.visit_type(&node.r#type)?;
        self.let_binding_context
            .add(&node.name.name, node.r#type.as_ref().into());
        Ok(())
    }

    /// Visit a type item.
    ///
    /// This function ensures that all members of the type are defined.
    pub fn visit_type_item(&mut self, node: &'ast TypeItem) -> TypeResult<()> {
        for member in &node.members {
            self.visit_type_member(member)?;
        }
        Ok(())
    }

    /// Visit a type member.
    ///
    /// This function ensures that the type of the member is defined.
    fn visit_type_member(&mut self, node: &'ast TypeMemberItem) -> TypeResult<()> {
        self.visit_type(&node.r#type)?;
        Ok(())
    }

    /// Visit a statement.
    pub fn visit_stmt(&mut self, node: &'ast Stmt) -> TypeResult<()> {
        match node {
            Stmt::Let(l) => self.visit_let_stmt(l),
            _ => Ok(()),
        }
    }

    /// Visit a let statement.
    ///
    /// We either take the expected type of the let statement, or we infer the type of the variable
    /// from the expression.
    pub fn visit_let_stmt(&mut self, node: &'ast LetStmt) -> TypeResult<()> {
        let expected_ty = node
            .r#type
            .as_ref()
            .map(|t| t.as_ref().into())
            .unwrap_or(self.fresh_type_variable());
        let actual_ty = self.visit_expr(&node.value)?;
        self.unify(&expected_ty, &actual_ty)?;
        self.type_context.add(&node.name.name, actual_ty);
        Ok(())
    }

    /// Visit an expression.
    pub fn visit_expr(&mut self, node: &'ast Expr) -> TypeResult<Ty> {
        match node {
            Expr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            Expr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            Expr::Group(e) => self.visit_group_expr(e),
            Expr::Reference(e) => self.visit_reference_expr(e),
            _ => todo!(),
        }
    }

    /// Visit an integer literal expression.
    ///
    /// There is nothing to do here, other than infer that the type of the expression is i32.
    pub fn visit_integer_literal_expr(&mut self, _: &'ast IntegerLiteralExpr) -> TypeResult<Ty> {
        Ok(Ty::TConst("i32".to_owned()))
    }

    /// Visit a boolean literal expression.
    ///
    /// There is nothing to do here, other than infer that the type of the expression is bool.
    pub fn visit_boolean_literal_expr(&mut self, _: &'ast BooleanLiteralExpr) -> TypeResult<Ty> {
        Ok(Ty::TConst("bool".to_owned()))
    }

    /// Visit a group expression.
    ///
    /// This function ensures that the type of the inner expression is defined.
    pub fn visit_group_expr(&mut self, node: &'ast GroupExpr) -> TypeResult<Ty> {
        self.visit_expr(&node.inner)
    }

    /// Visit a reference expression.
    ///
    /// This function ensures that the type of the reference is defined.
    pub fn visit_reference_expr(&mut self, node: &'ast ReferenceExpr) -> TypeResult<Ty> {
        let ty = self.search_let_binding(&node.name.name, &node.name.span)?;
        Ok(ty.clone())
    }

    /// Visit a type.
    ///
    /// This function ensures that the type is defined in the current scope.
    fn visit_type(&mut self, node: &'ast Type) -> TypeResult<()> {
        match node {
            Type::Named(t) => {
                self.search_type(&t.name.name, &t.name.span)?;
            }
            Type::Pointer(t) => self.visit_type(&t.inner)?,
            Type::Reference(t) => self.visit_type(&t.inner)?,
            Type::Boolean(_) => {
                self.search_type("bool", node.span())?;
            }
            Type::Integer32(_) => {
                self.search_type("i32", node.span())?;
            }
            Type::Unit(_) => {
                self.search_type("void", node.span())?;
            }
        };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::error::{
        InvalidTypeReferenceError, InvalidValueReferenceError, TypeError, TypeResult,
    };
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
    fn test_record_fields_are_typed() {
        assert_ok!(assert_type_check(
            r#"
        type Delta = { a: Point, b: Point, }
        type Point = { x: i32, y: i32, }
        intrinsic_type i32;
        "#
        ));
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
    fn test_invalid_value_reference_fails_type_check() {
        let err = assert_err!(assert_type_check(
            r#"
        intrinsic_type i32;
        fn foo(x: i32) {
          let a = k;
        }
        "#
        ));
        assert!(
            matches!(err, TypeError::InvalidValueReference(InvalidValueReferenceError {
            name,
            ..
            }) if name == "k")
        );
    }

    #[test]
    fn test_type_parameters_are_substituted_in_fn() {
        assert_ok!(assert_type_check(
            r#"
        fn foo<T>(x: T) -> T {}
        "#
        ));

        assert_ok!(assert_type_check(
            r#"
        fn foo<K>(x: T) -> T {}
        type T = { x: i32, }
        intrinsic_type i32;
        "#
        ));

        let err = assert_err!(assert_type_check(
            r#"
        fn foo<T>(x: U) -> T {}
        "#
        ));
        assert!(
            matches!(err, TypeError::InvalidTypeReference(InvalidTypeReferenceError {
            name,
            ..
        }) if name == "U")
        );
    }
}
