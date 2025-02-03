mod typing_context;

use crate::hir::{
    HirAddressOfExpr, HirAssignExpr, HirBooleanLiteralExpr, HirCallExpr, HirCallableReferenceExpr,
    HirCallableSymbol, HirConstantIndexExpr, HirConstructExpr, HirDerefExpr, HirExpr, HirFunction,
    HirGroupExpr, HirInstance, HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr,
    HirStruct, HirTrait,
};
use crate::hir::{
    HirBlockStmt, HirExprStmt, HirFunctionTy, HirIfStmt, HirLetStmt, HirLoopStmt, HirModule,
    HirPointerTy, HirReturnStmt, HirStmt, HirTy,
};
use crate::hir_builder::HirBuilder;
use crate::hir_error::{
    HirError, HirResult, InvalidReferenceError, TypeFieldInfiniteRecursionError, UnknownTypeError,
    WrongTraitTypeArgumentCount,
};
use eight_diagnostics::ice;
use eight_span::Span;
use std::collections::BTreeMap;
use std::fmt::Debug;
pub use typing_context::TypingContext;

#[derive(Debug)]
pub enum Constraint<'hir> {
    Equality(EqualityConstraint<'hir>),
    FieldProjection(FieldProjectionConstraint<'hir>),
    Instance(InstanceConstraint<'hir>),
    Method(MethodConstraint<'hir>),
    Dereferenceable(DereferenceableConstraint<'hir>),
}

/// Represent a constraint that two types have to be equal.
#[derive(Debug)]
pub struct EqualityConstraint<'hir> {
    /// The type that was expected, generally the left-hand side
    pub expectation: &'hir HirTy<'hir>,
    pub expectation_loc: Span,
    /// The type that wa mut  actually found, generally the right-hand side
    pub actual: &'hir HirTy<'hir>,
    pub actual_loc: Span,
}

/// Represent a field projection constraint.
///
/// This constraint requires the `origin` type to resolve to a struct type that has a field with the
/// given name N. The Nth field of the struct is then constrained to be equal to the
/// `resolved_type`.
#[derive(Debug)]
pub struct FieldProjectionConstraint<'hir> {
    pub origin: &'hir HirTy<'hir>,
    pub field: &'hir str,
    pub field_span: Span,
    pub expectation: &'hir HirTy<'hir>,
}

/// Represent a type class instance constraint.
///
/// This constraint requires that there exists an instance of trait `name` with the given type
/// parameters.
///
/// TODO: Consider making a separate receiver field.
#[derive(Debug)]
pub struct InstanceConstraint<'hir> {
    pub name: &'hir str,
    pub name_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub expectation: &'hir HirTy<'hir>,
}

/// Represent a method constraint.
///
/// A method constraint simply says that some function must exist, accepting the following types.
///
/// TODO: Consider making a separate receiver field.
#[derive(Debug)]
pub struct MethodConstraint<'hir> {
    pub name: &'hir str,
    pub name_span: &'hir str,
    pub argument_types: Vec<&'hir HirTy<'hir>>,
    pub expectation: &'hir HirTy<'hir>,
}

/// A constraint that a type is dereferenceable.
///
/// Today, this simply means that the type is a pointer type.
#[derive(Debug)]
pub struct DereferenceableConstraint<'hir> {
    /// The type that is dereferenceable
    pub ty: &'hir HirTy<'hir>,
    /// The type that it should dereference into
    pub expectation: &'hir HirTy<'hir>,
    pub span: Span,
}

/// Replace the $expr node with the result of $app if it changed, optionally wrapped in the function
/// $gen.
macro_rules! substitute_if_changed {
    ($expr:expr, $app:expr) => {
        if let Some(next) = $app {
            let _ = std::mem::replace($expr, next);
        }
    };
    ($expr:expr, $app:expr, $gen:expr) => {
        if let Some(next) = $app {
            let _ = std::mem::replace($expr, $gen(next));
        }
    };
}

pub struct HirModuleTypeCheckerPass();

impl HirModuleTypeCheckerPass {
    /// Type-check and perform type inference on the given module.
    pub fn visit<'hir>(
        module: &mut HirModule<'hir>,
        cx: &mut TypingContext<'hir>,
    ) -> HirResult<()> {
        cx.enter_let_binding_scope();
        Self::visit_module_functions(cx, &mut module.body.functions)?;
        Self::visit_module_structs(cx, &mut module.body.structs)?;
        Self::visit_module_traits(cx, &mut module.body.traits)?;
        for instance in module.body.instances.iter_mut() {
            Self::visit_instance(cx, instance)?;
        }
        cx.leave_let_binding_scope();
        Ok(())
    }

    pub fn visit_module_functions<'hir>(
        cx: &mut TypingContext<'hir>,
        functions: &mut BTreeMap<&'hir str, HirFunction<'hir>>,
    ) -> HirResult<()> {
        for fun in functions.values_mut() {
            Self::visit_function(cx, fun)?;
        }
        Ok(())
    }

    pub fn visit_module_structs<'hir>(
        cx: &mut TypingContext<'hir>,
        structs: &mut BTreeMap<&'hir str, HirStruct<'hir>>,
    ) -> HirResult<()> {
        for rec in structs.values_mut() {
            Self::visit_struct(cx, rec)?;
        }
        Ok(())
    }

    pub fn visit_module_traits<'hir>(
        cx: &mut TypingContext<'hir>,
        traits: &mut BTreeMap<&'hir str, HirTrait<'hir>>,
    ) -> HirResult<()> {
        for rec in traits.values_mut() {
            Self::visit_trait(cx, rec)?;
        }
        Ok(())
    }

    /// Traverse the function.
    ///
    /// This ensures the types of the function's parameters and return type are correct, then it
    /// recurses down into the function body.
    pub fn visit_function<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirFunction<'hir>,
    ) -> HirResult<()> {
        cx.enter_type_binding_scope();
        // Instantiate all the HirTy::Variable types from the function's type variables
        for type_parameter in node.signature.type_parameters.iter() {
            let ty = cx.instantiate_type_parameter(type_parameter.ty);
            node.type_parameter_substitutions
                .insert(type_parameter.name, ty);
        }

        // Propagate the parameter and return types. If any of these are HirTy::Variable, they are
        // replaced with their HirTy::Meta substitution.
        node.instantiated_return_type = Some(Self::visit_type(cx, node.signature.return_type)?);
        for p in node.signature.parameters.iter() {
            let ty = Self::visit_type(cx, p.ty)?;
            node.instantiated_parameters.insert(p.name, ty);
        }

        // Push the function's type onto the current stack, so that return statements can be checked
        // against the expected return type.
        let HirTy::Function(self_ty) = cx.cc.hir_function_type(
            node.instantiated_return_type
                .unwrap_or_else(|| ice!("freshly built return type was missing")),
            node.instantiated_parameters.values().copied().collect(),
        ) else {
            ice!("freshly built function type should be a function");
        };
        // NOTE: This function call cannot be moved further up, because the return type and args of
        // this function must have been visited first.
        cx.record_function_context_entry(self_ty);
        cx.enter_let_binding_scope();
        // Push all the function parameters into the local context.
        for (p, (name, ty)) in node
            .signature
            .parameters
            .iter()
            .zip(node.instantiated_parameters.iter())
        {
            cx.record_let_binding(name, p.span, ty)?;
        }
        // Type inference is done in two passes. First, we collect all the constraints for all the
        // child nodes of the function body, then we solve the type constraints, and finally we
        // traverse once more to perform substitution of each node.
        for stmt in node.body.iter_mut() {
            if let Some(next) = Self::enter_stmt(cx, stmt)? {
                let _ = std::mem::replace(stmt, next);
            }
        }
        cx.solve_constraints()?;
        for stmt in node.body.iter_mut() {
            if let Some(next) = Self::leave_stmt(cx, stmt)? {
                let _ = std::mem::replace(stmt, next);
            }
        }
        cx.leave_let_binding_scope();
        cx.record_function_context_exit();
        cx.leave_type_binding_scope();
        cx.reset_substitutions();
        Ok(())
    }

    /// Visit a struct.
    ///
    /// This ensures that all the struct fields are valid, and that the struct is not recursive.
    ///
    /// A struct type is infinitely recursive if any of its fields are unable to break the cycle.
    /// Types that can be break the cycle are pointer types. This means that if a type directly
    /// references itself by name
    pub fn visit_struct<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirStruct<'hir>,
    ) -> HirResult<()> {
        // Instantiate the types of the struct fields.
        for field in node.signature.fields.values() {
            let ty = Self::visit_type(cx, field.ty)?;
            node.instantiated_fields.insert(field.name, ty);
        }

        for (field_name, field_declaration) in node.signature.fields.iter() {
            let field_ty = node.instantiated_fields.get(field_name).unwrap_or_else(|| {
                ice!(format!(
                    "field {} not found in struct type {}",
                    field_name, node.name
                ))
            });
            let is_directly_self_referential =
                matches!(field_ty, HirTy::Nominal(n) if std::ptr::eq(n.name, node.name));
            if is_directly_self_referential {
                return Err(HirError::TypeFieldInfiniteRecursion(
                    TypeFieldInfiniteRecursionError {
                        type_name: node.name.to_owned(),
                        offending_field: (*field_name).to_owned(),
                        span: field_declaration.span,
                    },
                ));
            }
        }
        Ok(())
    }

    /// Visit a trait.
    ///
    /// Because trait functions are all ambient declarations, there is nothing to recurse down.
    /// Instead, we just ensure that the types that are being referred to are well
    pub fn visit_trait<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirTrait<'hir>,
    ) -> HirResult<()> {
        cx.enter_type_binding_scope();
        // Push the trait type parameters onto the substitution stack. As with `visit_function`,
        // this makes the `T` in `trait Foo<T> {}` visible to the trait body. While there are no let
        // bindings in traits because they are ambient, methods can still use these types.
        for type_parameter in node.signature.type_parameters.iter() {
            cx.instantiate_type_parameter(type_parameter.ty);
        }

        // Iterate through the ambient method declarations
        for method in node.signature.methods.values() {
            cx.enter_type_binding_scope();
            // Push all the type arguments of the method onto the substitution stack, allowing the
            // parameters and return type to refer to them.
            for type_parameter in method.type_parameters.iter() {
                cx.instantiate_type_parameter(type_parameter.ty);
            }
            // It is impossible that these types are uninitialized.
            Self::visit_type(cx, method.return_type)?;
            for parameter in method.parameters.iter() {
                // It is impossible that these types are uninitialized.
                Self::visit_type(cx, parameter.ty)?;
            }
            cx.leave_type_binding_scope();
        }
        cx.leave_type_binding_scope();
        Ok(())
    }

    /// Visit an instance.
    ///
    /// An instance essentially only acts as a type scope for its methods. That means we can simply
    /// call `visit_function` on each method once we've taken care of the prep-work for the trait
    /// itself.
    ///
    /// TODO: When traits become generic, we need to instantiate all parameter types from the traits
    ///   in this function.
    pub fn visit_instance<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirInstance<'hir>,
    ) -> HirResult<()> {
        // We acquire the trait's type parameters, and match the substitutions to the type arguments
        // the current instance instantiates them with.
        cx.enter_type_binding_scope();

        // Ensure and substitute all the trait type parameters with the instantiated type arguments
        // declared in the instance.
        for argument_index in 0..node.type_arguments.len() {
            // Match this type argument to the type parameters in the trait.
            let r#trait = cx
                .signature
                .query_trait_by_name(node.name)
                .unwrap_or_else(|| ice!(format!("trait {} not found", node.name)));

            // This is an ownership workaround. Ideally this should be checked above the loop, but
            // works here, because instances are syntactically required to have at least one type
            // argument.
            if argument_index == 0 && r#trait.type_parameters.len() != node.type_arguments.len() {
                return Err(HirError::WrongTraitTypeArgumentCount(
                    WrongTraitTypeArgumentCount {
                        expected: r#trait.type_parameters.len(),
                        actual: node.type_arguments.len(),
                        name: node.name.to_owned(),
                        span: node.name_span,
                        trait_declaration_loc: r#trait.name_span,
                    },
                ));
            }
            let Some(type_parameter) = r#trait.type_parameters.get(argument_index) else {
                ice!(format!(
                    "type parameter at position {} did not exist after check",
                    argument_index
                ));
            };
            // Hack around the borrow checker. This returns the exact same value, but the lifetime
            // of the reference is not tied to `r#trait` anymore.
            let name = cx.cc.intern_str(type_parameter.name);
            let span = type_parameter.span;
            debug_assert!(std::ptr::eq(type_parameter.name, name));
            let substitution = cx.fresh_meta_variable();
            cx.record_type_binding(name, span, substitution)?;
        }

        // Traverse down each of the methods in the instance.
        for method in node.members.iter_mut() {
            Self::visit_function(cx, method)?;
        }

        cx.leave_type_binding_scope();
        Ok(())
    }
}

impl HirModuleTypeCheckerPass {
    /// Visit a type.
    ///
    /// This ensures that the type is well-formed, and that it is not infinitely recursive.
    ///
    /// Because all uninitialized types are eliminated during type inference, we must replace all
    /// uninitialized types with fresh type variables here.
    pub fn visit_type<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &'hir HirTy<'hir>,
    ) -> HirResult<&'hir HirTy<'hir>> {
        match node {
            t @ HirTy::Nominal(_) => Self::visit_nominal_ty(cx, t),
            HirTy::Function(t) => Self::visit_function_ty(cx, t),
            HirTy::Pointer(t) => Self::visit_pointer_ty(cx, t),
            HirTy::Variable(v) => {
                match cx.type_parameter_instantiations.find(&(v.depth, v.index)) {
                    Some(ty) => Ok(ty),
                    None => ice!("referenced type variable was never instantiated"),
                }
            }
            HirTy::Integer32(_) | HirTy::Boolean(_) | HirTy::Unit(_) | HirTy::Meta(_) => Ok(node),
            // If the type was uninitialized by the lowering pass, we need to replace it with a
            // fresh type variable here.
            HirTy::Uninitialized(_) => {
                let v = cx.fresh_meta_variable();
                Ok(v)
            }
        }
    }

    /// A named type is either a user-defined struct, a builtin type, or a generic type parameter.
    ///
    /// If it is a generic type parameter, we substitute it with the matching substitution from the
    /// local type parameter substitution context.
    ///
    /// It is important that we check for local type parameter substitutions first, as they can
    /// shadow global names.
    pub fn visit_nominal_ty<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &'hir HirTy<'hir>,
    ) -> HirResult<&'hir HirTy<'hir>> {
        let HirTy::Nominal(n) = node else {
            ice!("visit_nominal_ty called with non-nominal type");
        };
        // Check if the name refers to a generic type parameter, like `T`.
        if let Some(sub) = cx.find_type_binding(n.name) {
            return Ok(sub);
        }
        // Check if the name refers to a struct or a type.
        if cx.signature.query_struct_by_name(n.name).is_some()
            || cx.signature.query_type_by_name(n.name).is_some()
        {
            return Ok(node);
        }
        // The type does not exist in the typing context, so the type is ill-formed.
        Err(HirError::UnknownType(UnknownTypeError {
            name: n.name.to_owned(),
            span: n.name_span,
        }))
    }

    /// Visit a function type.
    pub fn visit_function_ty<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &HirFunctionTy<'hir>,
    ) -> HirResult<&'hir HirTy<'hir>> {
        let parameters = node
            .parameters
            .iter()
            .map(|p| Self::visit_type(cx, p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type = Self::visit_type(cx, node.return_type)?;
        Ok(cx.cc.hir_function_type(return_type, parameters))
    }

    /// Visit a pointer type.
    pub fn visit_pointer_ty<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &'hir HirPointerTy<'hir>,
    ) -> HirResult<&'hir HirTy<'hir>> {
        let inner = Self::visit_type(cx, node.inner)?;
        Ok(cx.cc.hir_pointer_type(inner))
    }

    /// Collect type constraints for an expression.
    pub fn enter_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        match node {
            HirExpr::IntegerLiteral(e) => Self::enter_integer_literal_expr(cx, e),
            HirExpr::BooleanLiteral(e) => Self::enter_boolean_literal_expr(cx, e),
            HirExpr::Group(e) => Self::enter_group_expr(cx, e),
            HirExpr::Reference(e) => Self::enter_reference_expr(cx, e),
            HirExpr::CallableReference(e) => Self::enter_callable_reference_expr(cx, e),
            HirExpr::Assign(e) => Self::enter_assign_expr(cx, e),
            HirExpr::OffsetIndex(e) => Self::enter_offset_index_expr(cx, e),
            HirExpr::ConstantIndex(e) => Self::enter_constant_index_expr(cx, e),
            HirExpr::Call(e) => Self::enter_call_expr(cx, e),
            HirExpr::Construct(e) => Self::enter_construct_expr(cx, e),
            HirExpr::AddressOf(e) => Self::enter_address_of_expr(cx, e),
            HirExpr::Deref(e) => Self::enter_deref_expr(cx, e),
        }
    }

    /// Perform substitution for an expression.
    pub fn leave_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        match node {
            HirExpr::IntegerLiteral(e) => Self::leave_integer_literal_expr(cx, e),
            HirExpr::BooleanLiteral(e) => Self::leave_boolean_literal_expr(cx, e),
            HirExpr::Group(e) => Self::leave_group_expr(cx, e),
            HirExpr::Reference(e) => Self::leave_reference_expr(cx, e),
            HirExpr::CallableReference(e) => Self::leave_callable_reference_expr(cx, e),
            HirExpr::Assign(e) => Self::leave_assign_expr(cx, e),
            HirExpr::OffsetIndex(e) => Self::leave_offset_index_expr(cx, e),
            HirExpr::ConstantIndex(e) => Self::leave_constant_index_expr(cx, e),
            HirExpr::Call(e) => Self::leave_call_expr(cx, e),
            HirExpr::Construct(e) => Self::leave_construct_expr(cx, e),
            HirExpr::AddressOf(e) => Self::leave_address_of_expr(cx, e),
            HirExpr::Deref(e) => Self::leave_deref_expr(cx, e),
        }
    }

    /// Collect type constraints for an integer literal expression.
    ///
    /// Inference ensures that the integer literal is tied to the i32 type.
    pub fn enter_integer_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIntegerLiteralExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        cx.infer_integer_literal_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for an integer literal expression.
    pub fn leave_integer_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIntegerLiteralExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a boolean literal expression.
    ///
    /// [`infer_expr`] ensures that the boolean literal is tied to the boolean type.
    pub fn enter_boolean_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBooleanLiteralExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        cx.infer_boolean_literal_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a boolean literal expression.
    pub fn leave_boolean_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBooleanLiteralExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a group expression.
    ///
    /// The grouping expression's type is inferred from the inner expression.
    pub fn enter_group_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirGroupExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.inner,
            Self::enter_expr(cx, &mut node.inner)?,
            Box::new
        );
        cx.infer_group_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a group expression.
    pub fn leave_group_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirGroupExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.inner,
            Self::leave_expr(cx, &mut node.inner)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a reference expression.
    ///
    /// For a reference expression, we constrain it to the type of the local variable in the local
    /// context.
    ///
    /// This function also performs validation on the local lookup.
    pub fn enter_reference_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReferenceExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        // See if the name resolves to a local let-binding or a function name.
        let is_local_reference = cx.find_let_binding(node.name).is_some();
        let is_function_reference = cx.signature.query_function_by_name(node.name).is_some();

        // If this surely points to a function (remember let-bindings take priority because they
        // may shadow a function), we can add metadata to the expression.
        let is_definitely_function = is_function_reference && !is_local_reference;
        if is_definitely_function {
            let mut node = HirBuilder::build_callable_reference_expr(
                node.span,
                // TODO: This vec![] should be filled if we ever support stuff like
                // let k = id::<i32>
                HirCallableSymbol::new_function(node.name, node.name_span, vec![]),
                node.ty,
            );
            let ty = node.ty;
            cx.infer_callable_reference_expr(&mut node, ty)?;
            return Ok(Some(HirExpr::CallableReference(node)));
        }

        // If we don't know where this name comes from, we have a type error.
        if !is_local_reference && !is_function_reference {
            return Err(HirError::InvalidReference(InvalidReferenceError {
                name: node.name.to_owned(),
                span: node.name_span,
            }));
        }
        cx.infer_reference_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a reference expression.
    pub fn leave_reference_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReferenceExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a callable reference expression.
    ///
    /// This doesn't actually do anything, because we rewrite function calls and references to these
    /// after the types have been inferred.
    pub fn enter_callable_reference_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallableReferenceExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.symbol,
            Self::enter_callable_symbol(cx, &mut node.symbol)?
        );
        cx.infer_callable_reference_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a callable reference expression.
    ///
    /// Same explanation as `enter_callable_reference_expr`.
    pub fn leave_callable_reference_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallableReferenceExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = cx.substitute(node.ty)?;
        substitute_if_changed!(
            &mut node.symbol,
            Self::leave_callable_symbol(cx, &mut node.symbol)?
        );
        Ok(None)
    }

    pub fn enter_callable_symbol<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallableSymbol<'hir>,
    ) -> HirResult<Option<HirCallableSymbol<'hir>>> {
        match node {
            HirCallableSymbol::Function(sym) => {
                for argument in sym.type_arguments.iter_mut() {
                    *argument = Self::visit_type(cx, argument)?;
                }
            }
            HirCallableSymbol::TraitFunction(sym) => {
                for argument in sym.trait_type_arguments.iter_mut() {
                    *argument = Self::visit_type(cx, argument)?;
                }
                for argument in sym.method_type_arguments.iter_mut() {
                    *argument = Self::visit_type(cx, argument)?;
                }
            }
        }
        Ok(None)
    }

    pub fn leave_callable_symbol<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallableSymbol<'hir>,
    ) -> HirResult<Option<HirCallableSymbol<'hir>>> {
        match node {
            HirCallableSymbol::Function(sym) => {
                for argument in sym.type_arguments.iter_mut() {
                    *argument = cx.substitute(argument)?;
                }
            }
            HirCallableSymbol::TraitFunction(sym) => {
                for argument in sym.trait_type_arguments.iter_mut() {
                    *argument = cx.substitute(argument)?;
                }
                for argument in sym.method_type_arguments.iter_mut() {
                    *argument = cx.substitute(argument)?;
                }
            }
        }
        Ok(None)
    }

    /// Collect type constraints for an assign expression.
    ///
    /// In order to prevent chaining of assignment such as `a = b = c`, we simply infer the type of
    /// the entire expression to be void.
    pub fn enter_assign_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAssignExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.lhs,
            Self::enter_expr(cx, &mut node.lhs)?,
            Box::new
        );
        substitute_if_changed!(
            &mut node.rhs,
            Self::enter_expr(cx, &mut node.rhs)?,
            Box::new
        );
        cx.infer_assign_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for an assignment expression.
    pub fn leave_assign_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAssignExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.lhs,
            Self::leave_expr(cx, &mut node.lhs)?,
            Box::new
        );
        substitute_if_changed!(
            &mut node.rhs,
            Self::leave_expr(cx, &mut node.rhs)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for an offset index expression.
    ///
    /// Since offsets only work on pointer types, infer will constrain the origin to be a pointer,
    /// and the index to be an integer.
    pub fn enter_offset_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirOffsetIndexExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.origin,
            Self::enter_expr(cx, &mut node.origin)?,
            Box::new
        );
        substitute_if_changed!(
            &mut node.index,
            Self::enter_expr(cx, &mut node.index)?,
            Box::new
        );
        cx.infer_offset_index_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for an offset index expression.
    pub fn leave_offset_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirOffsetIndexExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.origin,
            Self::leave_expr(cx, &mut node.origin)?,
            Box::new
        );
        substitute_if_changed!(
            &mut node.index,
            Self::leave_expr(cx, &mut node.index)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a constant index expression.
    pub fn enter_constant_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstantIndexExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.origin,
            Self::enter_expr(cx, &mut node.origin)?,
            Box::new
        );
        Ok(None)
    }

    /// Perform substitution for a constant index expression.
    pub fn leave_constant_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstantIndexExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.origin,
            Self::leave_expr(cx, &mut node.origin)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a call expression.
    pub fn enter_call_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.callee,
            Self::enter_expr(cx, &mut node.callee)?,
            Box::new
        );
        for arg in node.arguments.iter_mut() {
            substitute_if_changed!(arg, Self::enter_expr(cx, arg)?);
        }
        cx.infer_call_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a call expression.
    pub fn leave_call_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.callee,
            Self::leave_expr(cx, &mut node.callee)?,
            Box::new
        );
        for arg in node.method_type_arguments.iter_mut() {
            *arg = cx.substitute(arg)?;
        }
        for arg in node.arguments.iter_mut() {
            substitute_if_changed!(arg, Self::leave_expr(cx, arg)?);
        }
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a construct expression.
    pub fn enter_construct_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstructExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        // Nothing to re-assign here. This is just a check that the type that is being constructed
        // actually exists.
        Self::visit_type(cx, node.callee)?;
        node.ty = Self::visit_type(cx, node.ty)?;
        for arg in node.arguments.iter_mut() {
            substitute_if_changed!(
                &mut arg.expr,
                Self::enter_expr(cx, arg.expr.as_mut())?,
                Box::new
            );
        }
        cx.infer_construct_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a construct expression.
    pub fn leave_construct_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstructExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = cx.substitute(node.ty)?;
        for arg in node.arguments.iter_mut() {
            substitute_if_changed!(
                &mut arg.expr,
                Self::leave_expr(cx, &mut arg.expr)?,
                Box::new
            );
        }
        Ok(None)
    }

    /// Collect type constraints for an address of expression.
    pub fn enter_address_of_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAddressOfExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.inner,
            Self::enter_expr(cx, &mut node.inner)?,
            Box::new
        );
        cx.infer_address_of_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for an address of expression.
    pub fn leave_address_of_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAddressOfExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.inner,
            Self::leave_expr(cx, &mut node.inner)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a deref expression.
    pub fn enter_deref_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirDerefExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(
            &mut node.inner,
            Self::enter_expr(cx, &mut node.inner)?,
            Box::new
        );
        cx.infer_deref_expr(node, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a deref expression.
    pub fn leave_deref_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirDerefExpr<'hir>,
    ) -> HirResult<Option<HirExpr<'hir>>> {
        substitute_if_changed!(
            &mut node.inner,
            Self::leave_expr(cx, &mut node.inner)?,
            Box::new
        );
        node.ty = cx.substitute(node.ty)?;
        Ok(None)
    }

    /// Collect type constraints for a statement.
    ///
    /// This function is responsible for collecting constraints for all the expressions in children
    /// of the node.
    ///
    /// In a second pass, we will perform substitution on the same expressions, after all the
    /// constraints have been collected.
    pub fn enter_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        match node {
            HirStmt::Let(s) => Self::enter_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::enter_expr_stmt(cx, e),
            HirStmt::Loop(l) => Self::enter_loop_stmt(cx, l),
            HirStmt::Return(r) => Self::enter_return_stmt(cx, r),
            HirStmt::If(i) => Self::enter_if_stmt(cx, i),
            HirStmt::Block(b) => Self::enter_block_stmt(cx, b),
            // Nothing to do for these nodes.
            HirStmt::Break(_) | HirStmt::Continue(_) => Ok(None),
        }
    }

    /// Perform substitution on the given statement.
    pub fn leave_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        match node {
            HirStmt::Let(s) => Self::leave_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::leave_expr_stmt(cx, e),
            HirStmt::Loop(l) => Self::leave_loop_stmt(cx, l),
            HirStmt::Return(r) => Self::leave_return_stmt(cx, r),
            HirStmt::If(i) => Self::leave_if_stmt(cx, i),
            HirStmt::Block(b) => Self::leave_block_stmt(cx, b),
            // Nothing to do for these nodes.
            HirStmt::Break(_) | HirStmt::Continue(_) => Ok(None),
        }
    }

    /// Collect type constraints for a let statement.
    ///
    /// When visiting a let binding, we first visit the type to replace any uninitialized types
    /// with a fresh type variable, then we update the type environment with the new type.
    pub fn enter_let_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLetStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        // Replace any uninitialized types with a fresh type variable.
        node.ty = Self::visit_type(cx, node.ty)?;
        substitute_if_changed!(&mut node.value, Self::enter_expr(cx, &mut node.value)?);
        cx.infer(&mut node.value, node.ty)?;
        // Propagate the type of the expression to the type of the let-binding
        node.ty = node.value.ty();
        cx.record_let_binding(node.name, node.span, node.ty)?;
        Ok(None)
    }

    /// Perform substitution for a let statement.
    pub fn leave_let_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLetStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(&mut node.value, Self::leave_expr(cx, &mut node.value)?);
        // Propagate the type of the expression to the type of the let-binding
        node.ty = node.value.ty();
        Ok(None)
    }

    /// Collect type constraints for an expression statement.
    pub fn enter_expr_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExprStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(&mut node.expr, Self::enter_expr(cx, &mut node.expr)?);
        Ok(None)
    }

    /// Perform substitution for an expression statement.
    pub fn leave_expr_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExprStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(&mut node.expr, Self::leave_expr(cx, &mut node.expr)?);
        Ok(None)
    }

    /// Collect type constraints for a loop statement.
    pub fn enter_loop_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLoopStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(
            &mut node.condition,
            Self::enter_expr(cx, &mut node.condition)?
        );
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.cc.hir_boolean_type())?;
        cx.enter_let_binding_scope();
        for stmt in node.body.iter_mut() {
            substitute_if_changed!(stmt, Self::enter_stmt(cx, stmt)?);
        }
        cx.leave_let_binding_scope();
        Ok(None)
    }

    /// Perform substitution for a loop statement.
    pub fn leave_loop_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLoopStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(
            &mut node.condition,
            Self::leave_expr(cx, &mut node.condition)?
        );
        Self::leave_expr(cx, &mut node.condition)?;
        for stmt in node.body.iter_mut() {
            substitute_if_changed!(stmt, Self::leave_stmt(cx, stmt)?);
        }
        Ok(None)
    }

    /// Collect type constraints for a block statement.
    pub fn enter_block_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBlockStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        cx.enter_let_binding_scope();
        for stmt in node.body.iter_mut() {
            substitute_if_changed!(stmt, Self::enter_stmt(cx, stmt)?);
        }
        cx.leave_let_binding_scope();
        Ok(None)
    }

    /// Perform substitution for a block statement.
    pub fn leave_block_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBlockStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        for stmt in node.body.iter_mut() {
            substitute_if_changed!(stmt, Self::leave_stmt(cx, stmt)?);
        }
        Ok(None)
    }

    /// Collect type constraints for a break statement.
    pub fn enter_return_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReturnStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        if let Some(inner) = node.value.as_mut() {
            substitute_if_changed!(inner, Self::enter_expr(cx, inner)?);
            let parent = cx
                .find_function_context()
                // In the future syntax like this might be legal, but even then it should be caught in
                // the AST lowering pass.
                .unwrap_or_else(|| ice!("tried to infer return statement outside of function"));
            cx.infer(inner, parent.return_type)?;
        }
        Ok(None)
    }

    /// Perform substitution for a return statement.
    pub fn leave_return_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReturnStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        if let Some(inner) = node.value.as_mut() {
            substitute_if_changed!(inner, Self::leave_expr(cx, inner)?);
        }
        Ok(None)
    }

    /// Collect type constraints for an if statement.
    pub fn enter_if_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIfStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(
            &mut node.condition,
            Self::enter_expr(cx, &mut node.condition)?
        );
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.cc.hir_boolean_type())?;

        // Traverse down the happy path
        cx.enter_let_binding_scope();
        for stmt in node.happy_path.iter_mut() {
            substitute_if_changed!(stmt, Self::enter_stmt(cx, stmt)?);
        }
        cx.leave_let_binding_scope();

        // Traverse down the unhappy path
        cx.enter_let_binding_scope();
        for stmt in node.unhappy_path.iter_mut() {
            substitute_if_changed!(stmt, Self::enter_stmt(cx, stmt)?);
        }
        cx.leave_let_binding_scope();
        Ok(None)
    }

    pub fn leave_if_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIfStmt<'hir>,
    ) -> HirResult<Option<HirStmt<'hir>>> {
        substitute_if_changed!(
            &mut node.condition,
            Self::leave_expr(cx, &mut node.condition)?
        );
        Self::leave_expr(cx, &mut node.condition)?;
        for stmt in node.happy_path.iter_mut() {
            substitute_if_changed!(stmt, Self::leave_stmt(cx, stmt)?);
        }
        for stmt in node.unhappy_path.iter_mut() {
            substitute_if_changed!(stmt, Self::leave_stmt(cx, stmt)?);
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {}
