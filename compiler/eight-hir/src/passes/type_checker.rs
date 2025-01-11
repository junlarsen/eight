use crate::arena::HirArena;
use crate::context::LocalContext;
use crate::error::{
    FunctionTypeMismatchError, HirError, HirResult, InvalidFieldReferenceOfNonStructError,
    InvalidReferenceError, InvalidStructFieldReferenceError, MissingFieldError,
    SelfReferentialTypeError, TraitDoesNotExistError, TraitInstanceMissingFnError,
    TraitMissingInstanceError, TypeFieldInfiniteRecursionError, TypeMismatchError,
    UnknownFieldError, UnknownTypeError,
};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirDerefExpr, HirExpr, HirGroupExpr,
    HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp, HirUnaryOpExpr,
};
use crate::item::{HirFunction, HirInstance, HirStruct, HirTrait};
use crate::query::HirQueryDatabase;
use crate::signature::HirModuleSignature;
use crate::stmt::{
    HirBlockStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt, HirReturnStmt, HirStmt,
};
use crate::ty::{HirFunctionTy, HirPointerTy, HirTy, HirVariableTy};
use crate::HirModule;
use eight_diagnostics::ice;
use eight_span::Span;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::Debug;

#[derive(Debug)]
pub enum Constraint<'hir> {
    Equality(EqualityConstraint<'hir>),
    FieldProjection(FieldProjectionConstraint<'hir>),
    Instance(InstanceConstraint<'hir>),
}

/// Represent a constraint that two types have to be equal.
#[derive(Debug)]
pub struct EqualityConstraint<'hir> {
    /// The type that was expected, generally the left-hand side
    pub expectation: &'hir HirTy<'hir>,
    pub expectation_loc: Span,
    /// The type that was actually found, generally the right-hand side
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
/// This constraint requires that there exists an instance of trait `name` that for the given types
/// `type_arguments`.
#[derive(Debug)]
pub struct InstanceConstraint<'hir> {
    pub name: &'hir str,
    pub name_span: Span,
    pub method: &'hir str,
    pub method_span: Span,
    pub type_arguments: Vec<&'hir HirTy<'hir>>,
    pub expectation: &'hir HirTy<'hir>,
}

pub struct TypingContext<'hir> {
    /// A reference to the Hir arena for allocating types.
    arena: &'hir HirArena<'hir>,

    constraints: Vec<Constraint<'hir>>,
    /// The substitutions during unification.
    ///
    /// Indexed by (depth, index)
    substitutions: HashMap<(u32, u32), &'hir HirTy<'hir>>,
    /// The depth of the current type binding context.
    ///
    /// Used to generate the depth term of a fresh type variable. Whenever the type checker enters
    /// a new typing scope, it *must* increment this value, and reduce it when leaving the scope.
    type_binding_depth: u32,
    /// The index of the current type binding context.
    type_binding_index: u32,

    locals: LocalContext<&'hir HirTy<'hir>>,
    /// Type parameters that are currently being substituted in the current function.
    ///
    /// This is required when traversing function bodies, as we need to substitute `let x: T = 1;`
    /// with a matching type variable from the function's signature.
    ///
    /// We currently don't support nested functions or lambdas, so this does not necessarily have to
    /// be a VecDeque, but it's here for future use.
    local_type_parameter_substitutions: LocalContext<&'hir HirTy<'hir>>,
    current_function: VecDeque<&'hir HirFunctionTy<'hir>>,

    /// The signature of the module being type checked.
    module_signature: &'hir HirModuleSignature<'hir>,
    module_query_db: HirQueryDatabase<'hir>,
}

impl<'hir> Debug for TypingContext<'hir> {
    /// Debug implementation for TypingContext skipping the arena.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypingContext")
            .field("constraints", &self.constraints)
            .field("substitutions", &self.substitutions)
            .field("locals", &self.locals)
            .field(
                "local_type_parameter_substitutions",
                &self.local_type_parameter_substitutions,
            )
            .field("current_function", &self.current_function)
            .field("module_signature", &self.module_signature)
            .finish()
    }
}

impl<'hir> TypingContext<'hir> {
    pub fn new(
        arena: &'hir HirArena<'hir>,
        module_signature: &'hir HirModuleSignature<'hir>,
    ) -> Self {
        Self {
            arena,
            constraints: Vec::new(),
            substitutions: HashMap::new(),
            type_binding_depth: 0,
            type_binding_index: 0,
            locals: LocalContext::new(),
            local_type_parameter_substitutions: LocalContext::new(),
            current_function: VecDeque::new(),
            module_signature,
            module_query_db: HirQueryDatabase::new(module_signature),
        }
    }

    /// Imply a new field projection constraint
    pub fn constrain_field_projection(
        &mut self,
        origin: &'hir HirTy<'hir>,
        field: &'hir str,
        field_span: Span,
        expectation: &'hir HirTy<'hir>,
    ) {
        let constraint = Constraint::FieldProjection(FieldProjectionConstraint {
            origin,
            field,
            field_span,
            expectation,
        });
        self.constraints.push(constraint)
    }

    /// Imply a new equality constraint
    pub fn constrain_eq(
        &mut self,
        expectation: &'hir HirTy<'hir>,
        actual: &'hir HirTy<'hir>,
        expectation_loc: Span,
        actual_loc: Span,
    ) {
        self.constraints
            .push(Constraint::Equality(EqualityConstraint {
                expectation,
                actual,
                expectation_loc,
                actual_loc,
            }))
    }

    /// Imply a new instance constraint
    pub fn constrain_instance(
        &mut self,
        name: &'hir str,
        name_span: Span,
        method: &'hir str,
        method_span: Span,
        type_arguments: Vec<&'hir HirTy<'hir>>,
        expectation: &'hir HirTy<'hir>,
    ) {
        let constraint = Constraint::Instance(InstanceConstraint {
            name,
            name_span,
            method,
            method_span,
            type_arguments,
            expectation,
        });
        self.constraints.push(constraint)
    }

    /// Solve the constraints that have been implied on the context so far.
    pub fn solve_constraints(&mut self) -> HirResult<()> {
        let constraints = self.constraints.drain(..).collect::<Vec<_>>();

        for constraint in constraints {
            match constraint {
                Constraint::Equality(c) => self.unify_eq(c)?,
                Constraint::FieldProjection(c) => self.unify_field_projection(c)?,
                Constraint::Instance(c) => self.unify_instance(c)?,
            }
        }
        Ok(())
    }

    /// Perform unification of a field projection.
    ///
    /// A field projection constraint requires that the type `ty` is a struct type, and that the
    /// field `field` has type `inner`. This function unifies the two types.
    pub fn unify_field_projection(
        &mut self,
        constraint: FieldProjectionConstraint<'hir>,
    ) -> HirResult<()> {
        match constraint.origin {
            HirTy::Variable(v) if !self.is_substitution_equal_to_self(v) => {
                let constraint = FieldProjectionConstraint {
                    origin: self.substitute(constraint.origin)?,
                    field: constraint.field,
                    field_span: constraint.field_span,
                    expectation: constraint.expectation,
                };
                self.unify_field_projection(constraint)
            }
            HirTy::Nominal(n) => {
                let ty = self
                    .module_signature
                    .get_struct(n.name)
                    .unwrap_or_else(|| ice!("struct type not found"));
                let Some(struct_field) = ty.fields.get(constraint.field) else {
                    return Err(HirError::InvalidStructFieldReference(
                        InvalidStructFieldReferenceError {
                            type_name: n.name.to_owned(),
                            name: constraint.field.to_owned(),
                            span: constraint.field_span,
                        },
                    ));
                };
                let constraint = EqualityConstraint {
                    expectation: struct_field.ty,
                    expectation_loc: struct_field.span,
                    actual_loc: n.name_span,
                    actual: constraint.expectation,
                };
                self.unify_eq(constraint)?;
                Ok(())
            }
            _ => Err(HirError::InvalidFieldReferenceOfNonStruct(
                InvalidFieldReferenceOfNonStructError {
                    ty: constraint.origin.format(),
                    name: constraint.field.to_owned(),
                    span: constraint.field_span,
                },
            )),
        }
    }

    /// Perform unification of an instance constraint.
    ///
    /// An instance constraint requires that there exists an instance of trait `name` that for the
    /// given types `type_arguments`.
    pub fn unify_instance(&mut self, constraint: InstanceConstraint<'hir>) -> HirResult<()> {
        let _ =
            self.module_signature
                .get_trait(constraint.name)
                .ok_or(HirError::TraitDoesNotExist(TraitDoesNotExistError {
                    name: constraint.name.to_owned(),
                    span: constraint.name_span,
                }))?;
        let substitutions = constraint
            .type_arguments
            .iter()
            .map(|t| self.substitute(t))
            .collect::<HirResult<Vec<_>>>()?;
        let instance = self
            .module_query_db
            .query_trait_instance_by_name_and_type_arguments(
                constraint.name,
                substitutions.as_slice(),
            )
            .ok_or(HirError::TraitMissingInstance(TraitMissingInstanceError {
                instance_name: format!(
                    "{}{}",
                    constraint.name,
                    HirTy::format_substitutable_type_parameter_list(substitutions.as_slice())
                ),
                name: constraint.name.to_owned(),
                span: constraint.name_span,
            }))?;

        let method =
            instance
                .methods
                .get(constraint.method)
                .ok_or(HirError::TraitInstanceMissingFn(
                    TraitInstanceMissingFnError {
                        name: format!(
                            "{}{}",
                            constraint.method,
                            HirTy::format_substitutable_type_parameter_list(
                                substitutions.as_slice(),
                            )
                        ),
                        method: constraint.method.to_owned(),
                        span: constraint.method_span,
                    },
                ))?;
        let constraint = EqualityConstraint {
            expectation: constraint.expectation,
            actual: method.return_type,
            expectation_loc: Span::empty(),
            actual_loc: Span::empty(),
        };
        self.unify_eq(constraint)?;
        Ok(())
    }

    /// Perform unification of two types.
    ///
    /// Unification is the process of determining if two types can be unified into a single type.
    /// Because we currently do not support subtyping, this is always an equivalence check.
    pub fn unify_eq(
        &mut self,
        EqualityConstraint {
            expectation: expected,
            actual,
            expectation_loc: expected_loc,
            actual_loc,
        }: EqualityConstraint<'hir>,
    ) -> HirResult<()> {
        match (&expected, &actual) {
            (HirTy::Variable(lhs), HirTy::Variable(rhs))
                if lhs.depth == rhs.depth && lhs.index == rhs.index =>
            {
                Ok(())
            }
            (HirTy::Nominal(a), HirTy::Nominal(b)) if std::ptr::eq(a.name, b.name) => Ok(()),
            (HirTy::Variable(v), _) if !self.is_substitution_equal_to_self(v) => {
                let constraint = EqualityConstraint {
                    expectation: self
                        .substitution(v)
                        .unwrap_or_else(|| ice!("unreachable: tested variable no longer exists")),
                    actual,
                    expectation_loc: expected_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (_, HirTy::Variable(v)) if !self.is_substitution_equal_to_self(v) => {
                let constraint = EqualityConstraint {
                    expectation: expected,
                    actual: self
                        .substitution(v)
                        .unwrap_or_else(|| ice!("unreachable: tested variable no longer exists")),
                    expectation_loc: expected_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (HirTy::Variable(v), _) => {
                if self.occurs_in(v, actual) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: actual_loc,
                        right: expected_loc,
                    }));
                }
                self.substitutions.insert((v.depth, v.index), actual);
                Ok(())
            }
            (_, HirTy::Variable(v)) => {
                if self.occurs_in(v, expected) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: expected_loc,
                        right: actual_loc,
                    }));
                }
                self.substitutions.insert((v.depth, v.index), expected);
                Ok(())
            }
            (HirTy::Pointer(a), HirTy::Pointer(b)) => {
                let constraint = EqualityConstraint {
                    expectation: a.inner,
                    expectation_loc: expected_loc,
                    actual: b.inner,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (HirTy::Integer32(_), HirTy::Integer32(_)) => Ok(()),
            (HirTy::Boolean(_), HirTy::Boolean(_)) => Ok(()),
            (HirTy::Unit(_), HirTy::Unit(_)) => Ok(()),
            (HirTy::Function(definition), HirTy::Function(application)) => {
                if definition.parameters.len() != application.parameters.len() {
                    return Err(HirError::FunctionTypeMismatch(FunctionTypeMismatchError {
                        expected_ty: actual.format(),
                        span: expected_loc,
                    }));
                }
                let constraint = EqualityConstraint {
                    expectation: definition.return_type,
                    expectation_loc: expected_loc,
                    actual: application.return_type,
                    actual_loc,
                };
                self.unify_eq(constraint)?;
                for (parameter, argument) in definition
                    .parameters
                    .iter()
                    .zip(application.parameters.iter())
                {
                    let constraint = EqualityConstraint {
                        expectation: parameter,
                        expectation_loc: expected_loc,
                        actual: argument,
                        actual_loc,
                    };
                    self.unify_eq(constraint)?;
                }
                Ok(())
            }
            (HirTy::Uninitialized(_), _) | (_, HirTy::Uninitialized(_)) => {
                ice!("tried to unify with uninitialized type")
            }
            (lhs, rhs) => Err(HirError::TypeMismatch(TypeMismatchError {
                actual_loc,
                expected_loc,
                actual_type: rhs.format(),
                expected_type: lhs.format(),
            })),
        }
    }

    /// Create a fresh type variable.
    pub fn fresh_type_variable(&mut self) -> &'hir HirTy<'hir> {
        let depth = self.type_binding_depth;
        let index = self.type_binding_index;
        let ty = self.arena.types().get_variable_ty(depth, index);
        self.type_binding_index += 1;
        self.substitutions.insert((depth, index), ty);
        ty
    }

    /// Infer the type of an integer literal expression.
    pub fn infer_integer_literal_expr(
        &mut self,
        expr: &mut HirIntegerLiteralExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(
            expectation,
            self.arena.types().get_integer32_ty(),
            expr.span,
            expr.span,
        );
        Ok(())
    }

    /// Infer the type of a boolean literal expression.
    pub fn infer_boolean_literal_expr(
        &mut self,
        expr: &mut HirBooleanLiteralExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(
            expectation,
            self.arena.types().get_boolean_ty(),
            expr.span,
            expr.span,
        );
        Ok(())
    }

    /// Infer the type of an assign expression.
    pub fn infer_assign_expr(
        &mut self,
        expr: &mut HirAssignExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(
            expectation,
            self.arena.types().get_unit_ty(),
            expr.span,
            *expr.lhs.span(),
        );
        Ok(())
    }

    /// Infer the type of a reference expression.
    pub fn infer_reference_expr(
        &mut self,
        expr: &mut HirReferenceExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        // We attempt to look up a local variable first. This is cheaper than attempting to
        // instantiate a generic function.
        if let Some(local_ty) = self.locals.find(expr.name) {
            self.constrain_eq(expectation, local_ty, expr.span, expr.name_span);
            return Ok(());
        }

        // If the function refers to a function signature, we attempt to instantiate it if
        // it is generic.
        let Some(signature) = self.module_signature.get_function(expr.name) else {
            ice!("called infer() on a name that doesn't exist in the context");
        };
        // Non-generic functions are already "instantiated" and can be constrained directly.
        if signature.type_parameters.is_empty() {
            let parameters = signature
                .parameters
                .iter()
                .map(|p| p.ty)
                .collect::<Vec<_>>();
            let ty = self
                .arena
                .types()
                .get_function_ty(signature.return_type, parameters);
            self.constrain_eq(expectation, ty, expr.span, expr.name_span);
            return Ok(());
        }

        // Otherwise, we need to instantiate the generic parameters of the function, and
        // substitute the parameters and return types if they refer to one of the generic
        // type parameters.
        self.local_type_parameter_substitutions.enter_scope();
        for type_parameter in signature.type_parameters.iter() {
            let ty = self.fresh_type_variable();
            self.local_type_parameter_substitutions
                .add(type_parameter.name, ty);
        }
        // The types of the signature can refer to the type parameters at arbitrary depths,
        // e.g. `**T`, so we just recurse down to substitute.
        let parameters = signature
            .parameters
            .iter()
            .map(|p| HirModuleTypeCheckerPass::visit_type(self, p.ty))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type = HirModuleTypeCheckerPass::visit_type(self, signature.return_type)?;
        let ty = self.arena.types().get_function_ty(return_type, parameters);
        self.constrain_eq(expectation, ty, expr.span, expr.name_span);
        Ok(())
    }

    /// Infer the type of an offset index expression.
    pub fn infer_offset_index_expr(
        &mut self,
        expr: &mut HirOffsetIndexExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        // The index must be an integer type
        self.constrain_eq(
            self.arena.types().get_integer32_ty(),
            expr.index.ty(),
            expr.span,
            *expr.index.span(),
        );
        // The origin must be a pointer of the element type
        let elem_ptr_ty = self.arena.types().get_pointer_ty(expectation);
        self.constrain_eq(
            elem_ptr_ty,
            expr.origin.ty(),
            expr.span,
            *expr.origin.span(),
        );
        // The resulting type must be the element type
        self.constrain_eq(expectation, expr.ty, expr.span, *expr.origin.span());
        Ok(())
    }

    /// Infer the type of a constant index expression.
    pub fn infer_constant_index_expr(
        &mut self,
        expr: &mut HirConstantIndexExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(expectation, expr.ty, expr.span, *expr.origin.span());
        self.constrain_field_projection(expr.origin.ty(), expr.index, expr.index_span, expectation);
        Ok(())
    }

    /// Infer the type of a call expression.
    pub fn infer_call_expr(
        &mut self,
        expr: &mut HirCallExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        let expected_args = expr.arguments.iter().map(|a| a.ty()).collect::<Vec<_>>();
        let expected_signature = self
            .arena
            .types()
            .get_function_ty(expectation, expected_args);
        self.unify_eq(EqualityConstraint {
            expectation: expected_signature,
            actual: expr.callee.ty(),
            expectation_loc: expr.span,
            actual_loc: *expr.callee.span(),
        })?;

        // Constrain the return type of the expression to the wanted type
        self.unify_eq(EqualityConstraint {
            expectation,
            actual: expr.ty,
            expectation_loc: expr.span,
            actual_loc: *expr.callee.span(),
        })?;
        Ok(())
    }

    /// Infer the type of a construct expression.
    pub fn infer_construct_expr(
        &mut self,
        expr: &mut HirConstructExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        let HirTy::Nominal(n) = expr.callee else {
            ice!("construct expression callee is not a nominal type");
        };
        // TODO: Produce a proper diagnostic here
        let ty = self
            .module_signature
            .get_struct(n.name)
            .unwrap_or_else(|| ice!("struct type not found"));
        let mut visited_fields = HashSet::new();
        for provided_field in expr.arguments.iter() {
            let Some(field_definition) = ty.fields.get(&provided_field.field) else {
                return Err(HirError::UnknownField(UnknownFieldError {
                    field_name: provided_field.field.to_owned(),
                    type_name: n.name.to_owned(),
                    span: provided_field.field_span,
                }));
            };
            visited_fields.insert(provided_field.field);
            self.unify_eq(EqualityConstraint {
                actual: provided_field.expr.ty(),
                actual_loc: *provided_field.expr.span(),
                expectation: field_definition.ty,
                expectation_loc: field_definition.span,
            })?;
        }
        // If some of the fields from the struct are missing
        for field in ty.fields.values() {
            if !visited_fields.contains(field.name) {
                return Err(HirError::MissingField(MissingFieldError {
                    type_name: n.name.to_owned(),
                    field_name: field.name.to_owned(),
                    span: expr.span,
                    defined_at: field.span,
                }));
            }
        }
        // Constrain the expected type to the callee type, and the callee to the type being
        // constructed.
        self.unify_eq(EqualityConstraint {
            expectation: expr.ty,
            expectation_loc: expr.span,
            actual: expr.callee,
            actual_loc: expr.span,
        })?;
        self.unify_eq(EqualityConstraint {
            expectation: expr.ty,
            expectation_loc: expr.span,
            actual: expectation,
            actual_loc: expr.span,
        })?;
        Ok(())
    }

    /// Infer the type of an address of expression.
    pub fn infer_address_of_expr(
        &mut self,
        expr: &mut HirAddressOfExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        // &a means that e is *inner, and expectation is *inner
        let result_ty = self.arena.types().get_pointer_ty(expr.inner.ty());
        self.constrain_eq(expectation, result_ty, expr.span, *expr.inner.span());
        self.constrain_eq(expr.ty, result_ty, expr.span, *expr.inner.span());
        Ok(())
    }

    /// Infer the type of a deref expression.
    pub fn infer_deref_expr(
        &mut self,
        expr: &mut HirDerefExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        // *a means inner is a pointer type, and expected and e are unbox inner
        let inner_ptr = self.arena.types().get_pointer_ty(expectation);
        self.constrain_eq(expr.inner.ty(), inner_ptr, expr.span, *expr.inner.span());
        self.constrain_eq(expr.ty, expectation, expr.span, *expr.inner.span());
        Ok(())
    }

    /// Infer the type of a group expression.
    pub fn infer_group_expr(
        &mut self,
        expr: &mut HirGroupExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.infer(&mut expr.inner, expectation)?;
        self.constrain_eq(expectation, expr.ty, expr.span, *expr.inner.span());
        Ok(())
    }

    /// Infer the type of an unary operation expression.
    ///
    /// Unary operations traits are always fixed to two types: the operand type and the result type.
    ///
    /// This infers the following constraints:
    /// ```text
    /// Neg::neg<expr.ty, expectation>
    /// ```
    pub fn infer_unary_op_expr(
        &mut self,
        expr: &mut HirUnaryOpExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(expr.ty, expectation, expr.span, *expr.operand.span());
        let (trait_name, method_name) = match &expr.op {
            HirUnaryOp::Not => (self.arena.names().get("Not"), self.arena.names().get("not")),
            HirUnaryOp::Neg => (self.arena.names().get("Neg"), self.arena.names().get("neg")),
        };
        self.constrain_instance(
            trait_name,
            expr.span,
            method_name,
            expr.span,
            vec![expr.operand.ty(), expectation],
            expectation,
        );
        Ok(())
    }

    pub fn infer_binary_op_expr(
        &mut self,
        expr: &mut HirBinaryOpExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(
            expr.ty,
            expectation,
            expr.span,
            // TODO: is this correct?
            expr.span,
        );
        let (trait_name, method_name) = match &expr.op {
            HirBinaryOp::Add => (self.arena.names().get("Add"), self.arena.names().get("add")),
            HirBinaryOp::Sub => (self.arena.names().get("Sub"), self.arena.names().get("sub")),
            HirBinaryOp::Mul => (self.arena.names().get("Mul"), self.arena.names().get("mul")),
            HirBinaryOp::Div => (self.arena.names().get("Div"), self.arena.names().get("div")),
            HirBinaryOp::Rem => (self.arena.names().get("Rem"), self.arena.names().get("rem")),
            HirBinaryOp::Eq => (self.arena.names().get("Eq"), self.arena.names().get("eq")),
            HirBinaryOp::Neq => (self.arena.names().get("Eq"), self.arena.names().get("neq")),
            HirBinaryOp::Lt => (self.arena.names().get("Ord"), self.arena.names().get("lt")),
            HirBinaryOp::Gt => (self.arena.names().get("Ord"), self.arena.names().get("gt")),
            HirBinaryOp::Lte => (self.arena.names().get("Ord"), self.arena.names().get("lte")),
            HirBinaryOp::Gte => (self.arena.names().get("Ord"), self.arena.names().get("gte")),
            HirBinaryOp::And => (self.arena.names().get("And"), self.arena.names().get("and")),
            HirBinaryOp::Or => (self.arena.names().get("Or"), self.arena.names().get("or")),
        };
        self.constrain_instance(
            trait_name,
            expr.span,
            method_name,
            expr.span,
            vec![expr.lhs.ty(), expr.rhs.ty(), expectation],
            expectation,
        );
        Ok(())
    }

    /// Infer the expression's type based on its expected type.
    ///
    /// This collects the necessary constraints on the expression's type based on its structure. The
    /// constraints are solved in a post-order traversal of the expression tree once all the
    /// constraints of the current node and its children have been collected.
    pub fn infer(
        &mut self,
        expr: &mut HirExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        match expr {
            HirExpr::IntegerLiteral(e) => self.infer_integer_literal_expr(e, expectation),
            HirExpr::BooleanLiteral(e) => self.infer_boolean_literal_expr(e, expectation),
            HirExpr::Assign(e) => self.infer_assign_expr(e, expectation),
            HirExpr::Reference(e) => self.infer_reference_expr(e, expectation),
            HirExpr::OffsetIndex(e) => self.infer_offset_index_expr(e, expectation),
            HirExpr::ConstantIndex(e) => self.infer_constant_index_expr(e, expectation),
            HirExpr::Call(e) => self.infer_call_expr(e, expectation),
            HirExpr::Construct(e) => self.infer_construct_expr(e, expectation),
            HirExpr::AddressOf(e) => self.infer_address_of_expr(e, expectation),
            HirExpr::Deref(e) => self.infer_deref_expr(e, expectation),
            HirExpr::Group(e) => self.infer_group_expr(e, expectation),
            HirExpr::UnaryOp(e) => self.infer_unary_op_expr(e, expectation),
            HirExpr::BinaryOp(e) => self.infer_binary_op_expr(e, expectation),
        }
    }

    /// Perform the substitution step for a given type.
    ///
    /// This function substitutes any type variables in the given type with the matching type in the
    /// local substitution set $T, as long as the type variable is not equal to $T.
    pub fn substitute(&mut self, ty: &'hir HirTy<'hir>) -> HirResult<&'hir HirTy<'hir>> {
        match ty {
            // We substitute type variables as long as they don't point to $T
            HirTy::Variable(v)
                if !self
                    .substitution(v)
                    .map(|t| t.is_equal_to_variable(v))
                    .unwrap_or(false) =>
            {
                // We have to recurse down here, because $T could point to another type variable
                // that we may have a substitution for. e.g, $0 => $1 => i32
                let sub = self
                    .substitution(v)
                    .unwrap_or_else(|| ice!("unreachable: tested variable no longer exists"));
                Ok(self.substitute(sub)?)
            }
            // We substitute function types by substituting the return type and parameters
            HirTy::Function(f) => {
                let parameters = f
                    .parameters
                    .iter()
                    .map(|p| self.substitute(p))
                    .collect::<HirResult<Vec<_>>>()?;
                let return_type = self.substitute(f.return_type)?;
                Ok(self.arena.types().get_function_ty(return_type, parameters))
            }
            // We substitute pointer types by substituting the inner type
            HirTy::Pointer(p) => {
                let inner = self.substitute(p.inner)?;
                Ok(self.arena.types().get_pointer_ty(inner))
            }
            // Anything else is not a type variable or a constructor type, so there is nothing to
            // be done here.
            HirTy::Uninitialized(_) => ice!("uninitialized type should not be substituted"),
            HirTy::Integer32(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Variable(_)
            | HirTy::Nominal(_) => Ok(ty),
        }
    }

    /// Get the substitution for the given type variable.
    pub fn substitution(&self, v: &HirVariableTy) -> Option<&'hir HirTy<'hir>> {
        self.substitutions.get(&(v.depth, v.index)).copied()
    }

    /// Determine if the substitution at the given index is equal to its own type variable.
    pub fn is_substitution_equal_to_self(&self, v: &HirVariableTy) -> bool {
        self.substitution(v)
            .map(|t| t.is_equal_to_variable(v))
            .unwrap_or(false)
    }

    /// Determine if the given variable type occurs in another type.
    ///
    /// This is required for HM type inference, as we need to determine if a type variable points to
    /// itself. An example is a constraint like `$0 = fn() -> $0`, which cannot be satisfied ever.
    pub fn occurs_in(&self, v: &HirVariableTy, ty: &'hir HirTy<'hir>) -> bool {
        match ty {
            // If the variable points to a substitution of itself, it occurs in itself
            HirTy::Variable(o) if !self.is_substitution_equal_to_self(o) => true,
            HirTy::Variable(o) => o.depth == v.depth && o.index == v.index,
            HirTy::Function(t) => {
                self.occurs_in(v, t.return_type)
                    || t.parameters.iter().any(|p| self.occurs_in(v, p))
            }
            // Non-constructor types cannot possibly occur in other types.
            HirTy::Uninitialized(_) => ice!("uninitialized type should not be substituted"),
            HirTy::Integer32(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Nominal(_)
            | HirTy::Pointer(_) => false,
        }
    }
}

pub struct HirModuleTypeCheckerPass();

impl HirModuleTypeCheckerPass {
    /// Type-check and perform type inference on the given module.
    pub fn visit<'hir>(
        module: &mut HirModule<'hir>,
        cx: &mut TypingContext<'hir>,
    ) -> HirResult<()> {
        cx.locals.enter_scope();

        Self::visit_module_functions(cx, &mut module.body.functions)?;
        Self::visit_module_structs(cx, &mut module.body.structs)?;
        Self::visit_module_traits(cx, &mut module.body.traits)?;
        for instance in module.body.instances.iter_mut() {
            Self::visit_instance(cx, instance)?;
        }
        cx.locals.leave_scope();
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
        // Create substitutions for all the type parameters.
        cx.local_type_parameter_substitutions.enter_scope();
        cx.type_binding_depth += 1;
        cx.type_binding_index = 0;
        for type_parameter in node.signature.type_parameters.iter() {
            let substitution = cx.fresh_type_variable();
            node.type_parameter_substitutions
                .insert(type_parameter.name, substitution);
            cx.local_type_parameter_substitutions
                .add(type_parameter.name, substitution);
        }
        // Instantiate the types of the function parameters and return type.
        node.instantiated_return_type = Some(Self::visit_type(cx, node.signature.return_type)?);
        for p in node.signature.parameters.iter() {
            let ty = Self::visit_type(cx, p.ty)?;
            node.instantiated_parameters.insert(p.name, ty);
        }

        // Push the function's type onto the current stack, so that return statements can be checked
        // against the expected return type.
        let HirTy::Function(self_ty) = cx.arena.types().get_function_ty(
            node.instantiated_return_type
                .unwrap_or_else(|| ice!("freshly built return type was missing")),
            node.instantiated_parameters.values().copied().collect(),
        ) else {
            ice!("freshly built function type should be a function");
        };
        cx.current_function.push_back(self_ty);
        cx.locals.enter_scope();
        // Push all the function parameters into the local context.
        for (parameter_name, parameter_ty) in node.instantiated_parameters.iter() {
            cx.locals.add(parameter_name, parameter_ty);
        }
        // Type inference is done in two passes. First, we collect all the constraints for all the
        // child nodes of the function body, then we solve the type constraints, and finally we
        // traverse once more to perform substitution of each node.
        for stmt in node.body.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.solve_constraints()?;
        for stmt in node.body.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();
        cx.current_function.pop_back();
        cx.type_binding_depth -= 1;
        cx.type_binding_index = 0;
        cx.local_type_parameter_substitutions.leave_scope();
        cx.substitutions.clear();
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
        // Push the trait type parameters onto the substitution stack
        let depth_upon_function_entry = cx.type_binding_depth;
        cx.local_type_parameter_substitutions.enter_scope();
        for type_parameter in node.signature.type_parameters.iter() {
            let substitution = cx.fresh_type_variable();
            cx.local_type_parameter_substitutions
                .add(type_parameter.name, substitution);
        }

        // Iterate through the ambient method declarations
        for method in node.signature.methods.values() {
            // Push any method type parameters onto the substitution stack
            cx.local_type_parameter_substitutions.enter_scope();
            for type_parameter in method.type_parameters.iter() {
                let substitution = cx.fresh_type_variable();
                cx.local_type_parameter_substitutions
                    .add(type_parameter.name, substitution);
            }

            Self::visit_type(cx, method.return_type)?;
            for parameter in method.parameters.iter() {
                Self::visit_type(cx, parameter.ty)?;
            }

            cx.local_type_parameter_substitutions.leave_scope();
        }
        cx.local_type_parameter_substitutions.leave_scope();
        // Only clear substitutions that are related to the current De Bruijn depth. This ensures
        // that trait substitutions are not cleared when visiting methods in a trait with multiple
        // methods.
        cx.substitutions
            .retain(|(depth, _), _| *depth >= depth_upon_function_entry);
        Ok(())
    }

    /// Visit an instance.
    ///
    /// An instance essentially only acts as a type scope for its methods. That means we can simply
    /// call `visit_function` on each method once we've taken care of the prep-work for the trait
    /// itself.
    pub fn visit_instance<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirInstance<'hir>,
    ) -> HirResult<()> {
        // We acquire the trait's type parameters, and match the substitutions to the type arguments
        // the current instance instantiates them with.
        cx.local_type_parameter_substitutions.enter_scope();
        cx.type_binding_depth += 1;
        cx.type_binding_index = 0;
        for (argument_index, type_argument) in node.type_arguments.iter().enumerate() {
            // Match this type argument to the type parameters in the trait.
            let r#trait = cx
                .module_query_db
                .query_trait_by_name(node.name)
                .unwrap_or_else(|| ice!(format!("trait {} not found", node.name)));
            let Some(type_parameter) = r#trait.type_parameters.get(argument_index) else {
                ice!(format!(
                    "type parameter {} not found in trait {}",
                    type_argument, node.name
                ));
            };
            // Hack around the borrow checker. This returns the exact same value, but the lifetime
            // of the reference is not tied to `r#trait` anymore.
            let name = cx.arena.names().get(type_parameter.name);
            debug_assert!(std::ptr::eq(type_parameter.name, name));
            let substitution = cx.fresh_type_variable();
            cx.local_type_parameter_substitutions
                .add(name, substitution);
        }

        // Traverse down each of the methods in the instance.
        for method in node.members.iter_mut() {
            Self::visit_function(cx, method)?;
        }

        cx.type_binding_depth -= 1;
        cx.type_binding_index = 0;
        cx.local_type_parameter_substitutions.leave_scope();
        // TODO: If we ever support generics on a higher level, we need to do the same retrain as we
        //   do for functions.
        cx.substitutions.clear();
        Ok(())
    }

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
            HirTy::Variable(_) | HirTy::Integer32(_) | HirTy::Boolean(_) | HirTy::Unit(_) => {
                Ok(node)
            }
            // If the type was uninitialized by the lowering pass, we need to replace it with a
            // fresh type variable here.
            HirTy::Uninitialized(_) => {
                let v = cx.fresh_type_variable();
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
        if let Some(sub) = cx.local_type_parameter_substitutions.find(n.name) {
            return Ok(sub);
        }
        // Check if the name is a builtin or struct type.
        if cx.module_signature.get_type(n.name).is_some() {
            return Ok(node);
        }
        if cx.module_signature.get_struct(n.name).is_some() {
            return Ok(node);
        }
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
        Ok(cx.arena.types().get_function_ty(return_type, parameters))
    }

    /// Visit a pointer type.
    pub fn visit_pointer_ty<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &'hir HirPointerTy<'hir>,
    ) -> HirResult<&'hir HirTy<'hir>> {
        let inner = Self::visit_type(cx, node.inner)?;
        Ok(cx.arena.types().get_pointer_ty(inner))
    }

    /// Collect type constraints for an expression.
    pub fn enter_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExpr<'hir>,
    ) -> HirResult<()> {
        match node {
            HirExpr::IntegerLiteral(e) => Self::enter_integer_literal_expr(cx, e),
            HirExpr::BooleanLiteral(e) => Self::enter_boolean_literal_expr(cx, e),
            HirExpr::Group(e) => Self::enter_group_expr(cx, e),
            HirExpr::Reference(e) => Self::enter_reference_expr(cx, e),
            HirExpr::Assign(e) => Self::enter_assign_expr(cx, e),
            HirExpr::OffsetIndex(e) => Self::enter_offset_index_expr(cx, e),
            HirExpr::ConstantIndex(e) => Self::enter_constant_index_expr(cx, e),
            HirExpr::Call(e) => Self::enter_call_expr(cx, e),
            HirExpr::Construct(e) => Self::enter_construct_expr(cx, e),
            HirExpr::AddressOf(e) => Self::enter_address_of_expr(cx, e),
            HirExpr::Deref(e) => Self::enter_deref_expr(cx, e),
            HirExpr::UnaryOp(e) => Self::enter_unary_op_expr(cx, e),
            HirExpr::BinaryOp(e) => Self::enter_binary_op_expr(cx, e),
        }
    }

    /// Perform substitution for an expression.
    pub fn leave_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExpr<'hir>,
    ) -> HirResult<()> {
        match node {
            HirExpr::IntegerLiteral(e) => Self::leave_integer_literal_expr(cx, e),
            HirExpr::BooleanLiteral(e) => Self::leave_boolean_literal_expr(cx, e),
            HirExpr::Group(e) => Self::leave_group_expr(cx, e),
            HirExpr::Reference(e) => Self::leave_reference_expr(cx, e),
            HirExpr::Assign(e) => Self::leave_assign_expr(cx, e),
            HirExpr::OffsetIndex(e) => Self::leave_offset_index_expr(cx, e),
            HirExpr::ConstantIndex(e) => Self::leave_constant_index_expr(cx, e),
            HirExpr::Call(e) => Self::leave_call_expr(cx, e),
            HirExpr::Construct(e) => Self::leave_construct_expr(cx, e),
            HirExpr::AddressOf(e) => Self::leave_address_of_expr(cx, e),
            HirExpr::Deref(e) => Self::leave_deref_expr(cx, e),
            HirExpr::UnaryOp(e) => Self::leave_unary_op_expr(cx, e),
            HirExpr::BinaryOp(e) => Self::leave_binary_op_expr(cx, e),
        }
    }

    /// Collect type constraints for an integer literal expression.
    ///
    /// Inference ensures that the integer literal is tied to the i32 type.
    pub fn enter_integer_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIntegerLiteralExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        cx.infer_integer_literal_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for an integer literal expression.
    pub fn leave_integer_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIntegerLiteralExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a boolean literal expression.
    ///
    /// [`infer_expr`] ensures that the boolean literal is tied to the boolean type.
    pub fn enter_boolean_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBooleanLiteralExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        cx.infer_boolean_literal_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a boolean literal expression.
    pub fn leave_boolean_literal_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBooleanLiteralExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a group expression.
    ///
    /// The grouping expression's type is inferred from the inner expression.
    pub fn enter_group_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirGroupExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.inner)?;
        cx.infer_group_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a group expression.
    pub fn leave_group_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirGroupExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.inner)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
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
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        // See if the name resolves to a local let-binding or a function name.
        if cx.locals.find(node.name).is_none()
            && cx.module_signature.get_function(node.name).is_none()
        {
            return Err(HirError::InvalidReference(InvalidReferenceError {
                name: node.name.to_owned(),
                span: node.name_span,
            }));
        }
        cx.infer_reference_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a reference expression.
    pub fn leave_reference_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReferenceExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for an assign expression.
    ///
    /// In order to prevent chaining of assignment such as `a = b = c`, we simply infer the type of
    /// the entire expression to be void.
    pub fn enter_assign_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAssignExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.lhs)?;
        Self::enter_expr(cx, &mut node.rhs)?;
        cx.infer_assign_expr(node, node.ty)?;
        Ok(())
    }

    pub fn leave_assign_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAssignExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.lhs)?;
        Self::leave_expr(cx, &mut node.rhs)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for an offset index expression.
    ///
    /// Since offsets only work on pointer types, infer will constrain the origin to be a pointer,
    /// and the index to be an integer.
    pub fn enter_offset_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirOffsetIndexExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.origin)?;
        Self::enter_expr(cx, &mut node.index)?;
        cx.infer_offset_index_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for an offset index expression.
    pub fn leave_offset_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirOffsetIndexExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.origin)?;
        Self::leave_expr(cx, &mut node.index)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a constant index expression.
    pub fn enter_constant_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstantIndexExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.origin)?;
        cx.infer_constant_index_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a constant index expression.
    pub fn leave_constant_index_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstantIndexExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.origin)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a call expression.
    pub fn enter_call_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.callee)?;
        for arg in node.arguments.iter_mut() {
            Self::enter_expr(cx, arg)?;
        }
        cx.infer_call_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a call expression.
    pub fn leave_call_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirCallExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.callee)?;
        for arg in node.arguments.iter_mut() {
            Self::leave_expr(cx, arg)?;
        }
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a construct expression.
    pub fn enter_construct_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstructExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        for arg in node.arguments.iter_mut() {
            Self::enter_expr(cx, arg.expr.as_mut())?;
        }
        cx.infer_construct_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a construct expression.
    pub fn leave_construct_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirConstructExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = cx.substitute(node.ty)?;
        for arg in node.arguments.iter_mut() {
            Self::leave_expr(cx, &mut arg.expr)?;
        }
        Ok(())
    }

    /// Collect type constraints for an address of expression.
    pub fn enter_address_of_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAddressOfExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.inner)?;
        cx.infer_address_of_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for an address of expression.
    pub fn leave_address_of_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirAddressOfExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.inner)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a deref expression.
    pub fn enter_deref_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirDerefExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.inner)?;
        cx.infer_deref_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a deref expression.
    pub fn leave_deref_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirDerefExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.inner)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for an unary operation expression.
    pub fn enter_unary_op_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirUnaryOpExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.operand)?;
        Ok(())
    }

    /// Perform substitution for an unary operation expression.
    pub fn leave_unary_op_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirUnaryOpExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.operand)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
    }

    /// Collect type constraints for a binary operation expression.
    pub fn enter_binary_op_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBinaryOpExpr<'hir>,
    ) -> HirResult<()> {
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.lhs)?;
        Self::enter_expr(cx, &mut node.rhs)?;
        cx.infer_binary_op_expr(node, node.ty)?;
        Ok(())
    }

    /// Perform substitution for a binary operation expression.
    pub fn leave_binary_op_expr<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBinaryOpExpr<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.lhs)?;
        Self::leave_expr(cx, &mut node.rhs)?;
        node.ty = cx.substitute(node.ty)?;
        Ok(())
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
    ) -> HirResult<()> {
        match node {
            HirStmt::Let(s) => Self::enter_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::enter_expr_stmt(cx, e),
            HirStmt::Loop(l) => Self::enter_loop_stmt(cx, l),
            HirStmt::Return(r) => Self::enter_return_stmt(cx, r),
            HirStmt::If(i) => Self::enter_if_stmt(cx, i),
            HirStmt::Block(b) => Self::enter_block_stmt(cx, b),
            // Nothing to do for these nodes.
            HirStmt::Break(_) | HirStmt::Continue(_) => Ok(()),
        }
    }

    /// Perform substitution on the given statement.
    pub fn leave_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirStmt<'hir>,
    ) -> HirResult<()> {
        match node {
            HirStmt::Let(s) => Self::leave_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::leave_expr_stmt(cx, e),
            HirStmt::Loop(l) => Self::leave_loop_stmt(cx, l),
            HirStmt::Return(r) => Self::leave_return_stmt(cx, r),
            HirStmt::If(i) => Self::leave_if_stmt(cx, i),
            HirStmt::Block(b) => Self::leave_block_stmt(cx, b),
            // Nothing to do for these nodes.
            HirStmt::Break(_) | HirStmt::Continue(_) => Ok(()),
        }
    }

    /// Collect type constraints for a let statement.
    ///
    /// When visiting a let binding, we first visit the type to replace any uninitialized types
    /// with a fresh type variable, then we update the type environment with the new type.
    pub fn enter_let_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLetStmt<'hir>,
    ) -> HirResult<()> {
        // Replace any uninitialized types with a fresh type variable.
        node.ty = Self::visit_type(cx, node.ty)?;
        Self::enter_expr(cx, &mut node.value)?;
        cx.infer(&mut node.value, node.ty)?;
        // Propagate the type of the expression to the type of the let-binding
        node.ty = node.value.ty();
        cx.locals.add(node.name, node.ty);
        Ok(())
    }

    /// Perform substitution for a let statement.
    pub fn leave_let_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLetStmt<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.value)?;
        // Propagate the type of the expression to the type of the let-binding
        node.ty = node.value.ty();
        Ok(())
    }

    /// Collect type constraints for an expression statement.
    pub fn enter_expr_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExprStmt<'hir>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.expr)?;
        Ok(())
    }

    /// Perform substitution for an expression statement.
    pub fn leave_expr_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirExprStmt<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.expr)?;
        Ok(())
    }

    /// Collect type constraints for a loop statement.
    pub fn enter_loop_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLoopStmt<'hir>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.condition)?;
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.arena.types().get_boolean_ty())?;
        cx.locals.enter_scope();
        for stmt in node.body.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();
        Ok(())
    }

    /// Perform substitution for a loop statement.
    pub fn leave_loop_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirLoopStmt<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.condition)?;
        for stmt in node.body.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        Ok(())
    }

    /// Collect type constraints for a block statement.
    pub fn enter_block_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBlockStmt<'hir>,
    ) -> HirResult<()> {
        cx.locals.enter_scope();
        for stmt in node.body.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();
        Ok(())
    }

    /// Perform substitution for a block statement.
    pub fn leave_block_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirBlockStmt<'hir>,
    ) -> HirResult<()> {
        for stmt in node.body.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        Ok(())
    }

    /// Collect type constraints for a break statement.
    pub fn enter_return_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReturnStmt<'hir>,
    ) -> HirResult<()> {
        if let Some(inner) = node.value.as_mut() {
            Self::enter_expr(cx, inner)?;
            let parent = cx
                .current_function
                .front()
                // In the future syntax like this might be legal, but even then it should be caught in
                // the AST lowering pass.
                .unwrap_or_else(|| ice!("tried to infer return statement outside of function"));
            cx.infer(inner, parent.return_type)?;
        }
        Ok(())
    }

    /// Perform substitution for a return statement.
    pub fn leave_return_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirReturnStmt<'hir>,
    ) -> HirResult<()> {
        if let Some(inner) = node.value.as_mut() {
            Self::leave_expr(cx, inner)?;
        }
        Ok(())
    }

    /// Collect type constraints for an if statement.
    pub fn enter_if_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIfStmt<'hir>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.condition)?;
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.arena.types().get_boolean_ty())?;

        // Traverse down the happy path
        cx.locals.enter_scope();
        for stmt in node.happy_path.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();

        // Traverse down the unhappy path
        cx.locals.enter_scope();
        for stmt in node.unhappy_path.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();

        Ok(())
    }

    pub fn leave_if_stmt<'hir>(
        cx: &mut TypingContext<'hir>,
        node: &mut HirIfStmt<'hir>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.condition)?;
        for stmt in node.happy_path.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        for stmt in node.unhappy_path.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {}
