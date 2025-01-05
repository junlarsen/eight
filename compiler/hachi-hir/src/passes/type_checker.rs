use crate::context::LocalContext;
use crate::error::{
    FunctionTypeMismatchError, HirError, HirResult, InvalidFieldReferenceOfNonStructError,
    InvalidReferenceError, InvalidStructFieldReferenceError, SelfReferentialTypeError,
    TypeFieldInfiniteRecursionError, TypeMismatchError, UnknownTypeError,
};
use crate::expr::HirExpr;
use crate::fun::{HirFunction, HirFunctionSignature, HirIntrinsicFunction};
use crate::rec::HirRecord;
use crate::scalar::HirIntrinsicScalar;
use crate::stmt::{HirExprStmt, HirLetStmt, HirStmt};
use crate::ty::{HirFunctionTy, HirPointerTy, HirTy, HirTyArena};
use crate::{HirModule, HirName};
use hachi_diagnostics::ice;
use hachi_span::Span;
use std::collections::{BTreeMap, HashMap, VecDeque};

#[derive(Debug)]
pub enum Constraint<'ta> {
    Equality(EqualityConstraint<'ta>),
    FieldProjection(FieldProjectionConstraint<'ta>),
}

/// Represent a constraint that two types have to be equal.
#[derive(Debug)]
pub struct EqualityConstraint<'ta> {
    /// The type that was expected, generally the left-hand side
    pub expected: &'ta HirTy<'ta>,
    pub expected_loc: Span,
    /// The type that was actually found, generally the right-hand side
    pub actual: &'ta HirTy<'ta>,
    pub actual_loc: Span,
}

/// Represent a field projection constraint.
///
/// This constraint requires the `origin` type to resolve to a record type that has a field with the
/// given name N. The Nth field of the record is then constrained to be equal to the
/// `resolved_type`.
#[derive(Debug)]
pub struct FieldProjectionConstraint<'ta> {
    pub origin: &'ta HirTy<'ta>,
    pub field: HirName,
    pub resolved_type: &'ta HirTy<'ta>,
}

#[derive(Debug)]
pub struct TypingContext<'ta> {
    arena: &'ta HirTyArena<'ta>,
    constraints: Vec<Constraint<'ta>>,
    substitutions: Vec<&'ta HirTy<'ta>>,
    locals: LocalContext<&'ta HirTy<'ta>>,
    /// Type parameters that are currently being substituted in the current function.
    ///
    /// This is required when traversing function bodies, as we need to substitute `let x: T = 1;`
    /// with a matching type variable from the function's signature.
    ///
    /// We currently don't support nested functions or lambdas, so this does not necessarily have to
    /// be a VecDeque, but it's here for future use.
    local_type_parameter_substitutions: LocalContext<&'ta HirTy<'ta>>,
    current_function: VecDeque<&'ta HirFunctionTy<'ta>>,
    /// Types derived from the module that we are type checking.
    record_types: BTreeMap<String, HirRecord<'ta>>,
    scalar_types: BTreeMap<String, HirIntrinsicScalar<'ta>>,
    functions: BTreeMap<String, HirFunctionSignature<'ta>>,
}

impl<'ta> TypingContext<'ta> {
    pub fn new(arena: &'ta HirTyArena<'ta>) -> Self {
        Self {
            arena,
            constraints: Vec::new(),
            substitutions: Vec::new(),
            locals: LocalContext::new(),
            local_type_parameter_substitutions: LocalContext::new(),
            current_function: VecDeque::new(),
            scalar_types: BTreeMap::new(),
            functions: BTreeMap::new(),
            record_types: BTreeMap::new(),
        }
    }

    /// Imply a new field projection constraint
    pub fn constrain_field_projection(
        &mut self,
        ty: &'ta HirTy,
        field: HirName,
        inner: &'ta HirTy,
    ) {
        self.constraints
            .push(Constraint::FieldProjection(FieldProjectionConstraint {
                origin: ty,
                field,
                resolved_type: inner,
            }))
    }

    /// Imply a new equality constraint
    pub fn constrain_eq(
        &mut self,
        expected: &'ta HirTy<'ta>,
        actual: &'ta HirTy<'ta>,
        expected_loc: Span,
        actual_loc: Span,
    ) {
        self.constraints
            .push(Constraint::Equality(EqualityConstraint {
                expected,
                actual,
                expected_loc,
                actual_loc,
            }))
    }

    /// Solve the constraints that have been implied on the context so far.
    pub fn solve_constraints(&mut self) -> HirResult<()> {
        let constraints = self.constraints.drain(..).collect::<Vec<_>>();

        for constraint in constraints {
            match constraint {
                Constraint::Equality(c) => self.unify_eq(c)?,
                Constraint::FieldProjection(c) => self.unify_field_projection(c)?,
            }
        }
        Ok(())
    }

    /// Perform unification of a field projection.
    ///
    /// A field projection constraint requires that the type `ty` is a record type, and that the
    /// field `field` has type `inner`. This function unifies the two types.
    pub fn unify_field_projection(
        &mut self,
        FieldProjectionConstraint {
            origin,
            field,
            resolved_type,
        }: FieldProjectionConstraint<'ta>,
    ) -> HirResult<()> {
        match origin {
            HirTy::Variable(v) if !self.is_substitution_equal_to_self(v.var) => {
                let constraint = FieldProjectionConstraint {
                    origin: self.substitutions[v.var],
                    field,
                    resolved_type,
                };
                self.unify_field_projection(constraint)
            }
            HirTy::Nominal(n) => {
                let ty = self
                    .record_types
                    .get(&n.name.name)
                    .unwrap_or_else(|| ice!("record type not found"));
                let Some(record_field) = ty.fields.get(&field.name) else {
                    return Err(HirError::InvalidStructFieldReference(
                        InvalidStructFieldReferenceError {
                            type_name: n.name.name.to_owned(),
                            name: field.name.to_owned(),
                            span: field.span.clone(),
                        },
                    ));
                };
                let constraint = EqualityConstraint {
                    expected: record_field.r#type,
                    expected_loc: record_field.span.clone(),
                    actual_loc: n.name.span.clone(),
                    actual: resolved_type,
                };
                self.unify_eq(constraint)?;
                Ok(())
            }
            _ => Err(HirError::InvalidFieldReferenceOfNonStruct(
                InvalidFieldReferenceOfNonStructError {
                    ty: format!("{}", resolved_type),
                    name: field.name.to_owned(),
                    span: field.span.clone(),
                },
            )),
        }
    }

    /// Perform unification of two types.
    ///
    /// Unification is the process of determining if two types can be unified into a single type.
    /// Because we currently do not support subtyping, this is always an equivalence check.
    pub fn unify_eq(
        &mut self,
        EqualityConstraint {
            expected,
            actual,
            expected_loc,
            actual_loc,
        }: EqualityConstraint<'ta>,
    ) -> HirResult<()> {
        match (&expected, &actual) {
            (HirTy::Variable(lhs), HirTy::Variable(rhs)) if lhs.var == rhs.var => Ok(()),
            (HirTy::Nominal(a), HirTy::Nominal(b)) if a.name.name == b.name.name => Ok(()),
            (HirTy::Variable(v), _) if !self.is_substitution_equal_to_self(v.var) => {
                let constraint = EqualityConstraint {
                    expected: self.substitutions[v.var],
                    actual,
                    expected_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (_, HirTy::Variable(v)) if !self.is_substitution_equal_to_self(v.var) => {
                let constraint = EqualityConstraint {
                    expected,
                    actual: self.substitutions[v.var],
                    expected_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (HirTy::Variable(v), _) => {
                if self.occurs_in(v.var, actual) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: actual_loc,
                        right: expected_loc,
                    }));
                }
                self.substitutions[v.var] = actual;
                Ok(())
            }
            (_, HirTy::Variable(v)) => {
                if self.occurs_in(v.var, expected) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: expected_loc,
                        right: actual_loc,
                    }));
                }
                self.substitutions[v.var] = expected;
                Ok(())
            }
            (HirTy::Pointer(a), HirTy::Pointer(b)) => {
                let constraint = EqualityConstraint {
                    expected: a.inner,
                    expected_loc,
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
                        expected_ty: format!("{}", application),
                        span: expected_loc,
                    }));
                }
                let constraint = EqualityConstraint {
                    expected: definition.return_type,
                    expected_loc: expected_loc.clone(),
                    actual: application.return_type,
                    actual_loc: actual_loc.clone(),
                };
                self.unify_eq(constraint)?;
                for (parameter, argument) in definition
                    .parameters
                    .iter()
                    .zip(application.parameters.iter())
                {
                    let constraint = EqualityConstraint {
                        expected: parameter,
                        expected_loc: expected_loc.clone(),
                        actual: argument,
                        actual_loc: actual_loc.clone(),
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
                actual_type: format!("{}", rhs),
                expected_type: format!("{}", lhs),
            })),
        }
    }

    /// Create a fresh type variable.
    pub fn fresh_type_variable(&mut self) -> &'ta HirTy<'ta> {
        let ty = self.arena.get_variable_ty(self.substitutions.len());
        self.substitutions.push(ty);
        ty
    }

    /// Set up an expression for type inference.
    ///
    /// This function adds the necessary constraints to the expression's type based on its expected
    /// type. The expected type is typically a type variable.
    ///
    /// Note that this function doesn't perform any substitution, it simply declares the necessary
    /// constraints for the expression in preparation for substitution.
    pub fn infer(
        &mut self,
        expr: &mut HirExpr<'ta>,
        expected_ty: &'ta HirTy<'ta>,
    ) -> HirResult<()> {
        match expr {
            // Integer literals are always i32 at the moment
            HirExpr::IntegerLiteral(e) => {
                self.constrain_eq(
                    expected_ty,
                    self.arena.get_integer32_ty(),
                    e.span.clone(),
                    e.span.clone(),
                );
                Ok(())
            }
            // Booleans always have the bool type
            HirExpr::BooleanLiteral(e) => {
                self.constrain_eq(
                    expected_ty,
                    self.arena.get_boolean_ty(),
                    e.span.clone(),
                    e.span.clone(),
                );
                Ok(())
            }
            // We don't want assignments to be chained, so we infer them as unit
            HirExpr::Assign(e) => {
                self.constrain_eq(
                    expected_ty,
                    self.arena.get_unit_ty(),
                    e.span.clone(),
                    e.lhs.span().clone(),
                );
                Ok(())
            }
            HirExpr::Reference(e) => {
                // We attempt to look up a local variable first. This is cheaper than attempting to
                // instantiate a generic function.
                if let Some(local_ty) = self.locals.find(&e.name.name) {
                    self.constrain_eq(
                        expected_ty,
                        local_ty.clone(),
                        e.span.clone(),
                        e.name.span.clone(),
                    );
                    return Ok(());
                }

                // If the function refers to a function signature, we attempt to instantiate it if
                // it is generic.
                let Some(signature) = self.functions.get(&e.name.name) else {
                    ice!("called infer() on a name that doesn't exist in the context");
                };
                // Non-generic functions are already "instantiated" and can be constrained directly.
                if signature.type_parameters.is_empty() {
                    let parameters = signature
                        .parameters
                        .iter()
                        .map(|p| p.r#type)
                        .collect::<Vec<_>>();
                    let ty = self
                        .arena
                        .get_function_ty(signature.return_type, parameters);
                    self.constrain_eq(expected_ty, ty, e.span.clone(), e.name.span.clone());
                    return Ok(());
                }

                // Otherwise, we need to instantiate the generic parameters of the function, and
                // substitute the parameters and return types if they refer to one of the generic
                // type parameters.
                // TODO: Prevent this clone
                let signature = signature.clone();
                let mut type_parameter_substitutions = HashMap::new();
                for type_parameter in signature.type_parameters.iter() {
                    type_parameter_substitutions.insert(
                        type_parameter.syntax_name.name.to_owned(),
                        self.fresh_type_variable(),
                    );
                }
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|p| match &p.r#type {
                        HirTy::Nominal(n) => match type_parameter_substitutions.get(&n.name.name) {
                            Some(sub) => sub,
                            _ => p.r#type,
                        },
                        _ => p.r#type,
                    })
                    .collect::<Vec<_>>();
                let return_type = match &signature.return_type {
                    HirTy::Nominal(n) => match type_parameter_substitutions.get(&n.name.name) {
                        Some(sub) => sub,
                        _ => signature.return_type,
                    },
                    _ => signature.return_type,
                };
                let ty = self.arena.get_function_ty(return_type, parameters);
                self.constrain_eq(expected_ty, ty, e.span.clone(), e.name.span.clone());
                Ok(())
            }
            HirExpr::OffsetIndex(e) => {
                // The index must be an integer type
                self.constrain_eq(
                    self.arena.get_integer32_ty(),
                    e.index.ty(),
                    e.span.clone(),
                    e.index.span().clone(),
                );
                // The origin must be a pointer of the element type
                let elem_ptr_ty = self.arena.get_pointer_ty(expected_ty);
                self.constrain_eq(
                    elem_ptr_ty,
                    e.origin.ty(),
                    e.span.clone(),
                    e.origin.span().clone(),
                );
                // The resulting type must be the element type
                self.constrain_eq(expected_ty, e.ty, e.span.clone(), e.origin.span().clone());
                Ok(())
            }
            HirExpr::ConstantIndex(e) => {
                self.constrain_eq(expected_ty, e.ty, e.span.clone(), e.origin.span().clone());
                self.constrain_field_projection(e.origin.ty(), e.index.clone(), expected_ty);
                Ok(())
            }
            HirExpr::Call(e) => {
                let expected_args = e.arguments.iter().map(|a| a.ty()).collect::<Vec<_>>();
                let expected_signature = self.arena.get_function_ty(expected_ty, expected_args);
                self.unify_eq(EqualityConstraint {
                    expected: expected_signature,
                    actual: e.callee.ty(),
                    expected_loc: e.span.clone(),
                    actual_loc: e.callee.span().clone(),
                })?;

                // Constrain the return type of the expression to the wanted type
                self.unify_eq(EqualityConstraint {
                    expected: expected_ty,
                    actual: e.ty,
                    expected_loc: e.span.clone(),
                    actual_loc: e.callee.span().clone(),
                })?;
                Ok(())
            }
            HirExpr::Construct(e) => {
                let HirTy::Nominal(n) = e.callee else {
                    ice!("construct expression callee is not a nominal type");
                };
                let ty = self
                    .record_types
                    .get(&n.name.name)
                    .unwrap_or_else(|| ice!("record type not found"))
                    .clone();
                // TODO: Check that the number of arguments matches the number of fields
                let pairs = ty.fields.iter().zip(e.arguments.iter()).collect::<Vec<_>>();
                for ((_, expected_ty), arg) in pairs {
                    self.unify_eq(EqualityConstraint {
                        expected: arg.expr.ty(),
                        expected_loc: arg.expr.span().clone(),
                        actual: expected_ty.r#type,
                        actual_loc: expected_ty.span.clone(),
                    })?;
                }
                self.unify_eq(EqualityConstraint {
                    expected: e.ty,
                    expected_loc: e.span.clone(),
                    actual: e.callee,
                    actual_loc: e.span.clone(),
                })?;
                self.unify_eq(EqualityConstraint {
                    expected: e.ty,
                    expected_loc: e.span.clone(),
                    actual: expected_ty,
                    actual_loc: e.span.clone(),
                })?;
                Ok(())
            }
            HirExpr::AddressOf(e) => {
                // &a means that e is *inner, and expected_ty is *inner
                let result_ty = self.arena.get_pointer_ty(e.inner.ty());
                self.constrain_eq(
                    expected_ty,
                    result_ty,
                    e.span.clone(),
                    e.inner.span().clone(),
                );
                self.constrain_eq(e.ty, result_ty, e.span.clone(), e.inner.span().clone());
                Ok(())
            }
            HirExpr::Deref(e) => {
                // *a means inner is a pointer type, and expected and e are unbox inner
                let inner_ptr = self.arena.get_pointer_ty(expected_ty);
                self.constrain_eq(
                    e.inner.ty(),
                    inner_ptr,
                    e.span.clone(),
                    e.inner.span().clone(),
                );
                self.constrain_eq(e.ty, expected_ty, e.span.clone(), e.inner.span().clone());
                Ok(())
            }
            // Grouping expressions take the type of the inner expression
            HirExpr::Group(e) => {
                self.infer(&mut e.inner, expected_ty)?;
                Ok(())
            }
            HirExpr::UnaryOp(e) => todo!(),
            HirExpr::BinaryOp(e) => todo!(),
        }
    }

    /// Perform recursive substitution on an expression.
    ///
    /// This function recursively substitutes all type variables in the given expression and any
    /// subexpressions with the potentially matching types in the local substitution set.
    ///
    /// This is effectively another walk through the expression tree, but we do it separately here,
    /// so that we can bulk-substitute the entire expression tree at once. This is as opposed to
    /// substituting upon the walk during inference.
    ///
    /// TODO: Explain in doc comment why this is correct
    pub fn substitute_expr(&mut self, expr: &mut HirExpr<'ta>) -> HirResult<()> {
        match expr {
            HirExpr::IntegerLiteral(e) => {
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::BooleanLiteral(e) => {
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Reference(e) => {
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Assign(e) => {
                self.substitute_expr(&mut e.lhs)?;
                self.substitute_expr(&mut e.rhs)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::OffsetIndex(e) => {
                self.substitute_expr(&mut e.origin)?;
                self.substitute_expr(&mut e.index)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::ConstantIndex(e) => {
                self.substitute_expr(&mut e.origin)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Call(e) => {
                self.substitute_expr(&mut e.callee)?;
                for arg in e.arguments.iter_mut() {
                    self.substitute_expr(arg)?;
                }
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Construct(e) => {
                for arg in e.arguments.iter_mut() {
                    self.substitute_expr(arg.expr.as_mut())?;
                }
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::AddressOf(e) => {
                self.substitute_expr(&mut e.inner)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Deref(e) => {
                self.substitute_expr(&mut e.inner)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::Group(e) => {
                self.substitute_expr(&mut e.inner)?;
                e.ty = self.substitute(e.ty)?;
                Ok(())
            }
            HirExpr::UnaryOp(e) => todo!(),
            HirExpr::BinaryOp(e) => todo!(),
        }
    }

    /// Perform the substitution step for a given type.
    ///
    /// This function substitutes any type variables in the given type with the matching type in the
    /// local substitution set $T, as long as the type variable is not equal to $T.
    ///
    ///
    pub fn substitute(&mut self, ty: &'ta HirTy<'ta>) -> HirResult<&'ta HirTy<'ta>> {
        match ty {
            // We substitute type variables as long as they don't point to $T
            HirTy::Variable(v)
                if !self
                    .substitution(v.var)
                    .map(|t| t.is_equal_to_variable(v.var))
                    .unwrap_or(false) =>
            {
                // We have to recurse down here, because $T could point to another type variable
                // that we may have a substitution for.
                let sub = self.substitutions[v.var];
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
                Ok(self.arena.get_function_ty(return_type, parameters))
            }
            // We substitute pointer types by substituting the inner type
            HirTy::Pointer(p) => {
                let inner = self.substitute(p.inner)?;
                Ok(self.arena.get_pointer_ty(inner))
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
    pub fn substitution(&self, var: usize) -> Option<&'ta HirTy<'ta>> {
        self.substitutions.get(var).copied()
    }

    /// Determine if the substitution at the given index is equal to its own type variable.
    pub fn is_substitution_equal_to_self(&self, var: usize) -> bool {
        self.substitutions
            .get(var)
            .map(|t| t.is_equal_to_variable(var))
            .unwrap_or(false)
    }

    /// Determine if the given variable type occurs in another type.
    ///
    /// This is required for HM type inference, as we need to determine if a type variable points to
    /// itself. An example is a constraint like `$0 = fn() -> $0`, which cannot be satisfied ever.
    pub fn occurs_in(&self, var: usize, ty: &'ta HirTy<'ta>) -> bool {
        match ty {
            // If the variable points to a substitution of itself, it occurs in itself
            HirTy::Variable(v) if !self.is_substitution_equal_to_self(v.var) => true,
            HirTy::Variable(v) => v.var == var,
            HirTy::Function(t) => {
                self.occurs_in(var, t.return_type)
                    || t.parameters.iter().any(|p| self.occurs_in(var, p))
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

impl<'ta> TypingContext<'ta> {
    pub fn install_module_records(&mut self, records: &BTreeMap<String, HirRecord<'ta>>) {
        for rec in records.values() {
            self.record_types
                .insert(rec.name.name.to_owned(), rec.clone());
        }
    }

    pub fn install_module_functions(&mut self, functions: &BTreeMap<String, HirFunction<'ta>>) {
        let signatures = functions
            .iter()
            .map(|(name, fun)| (name.to_owned(), fun.signature()));
        for (name, signature) in signatures {
            self.functions.insert(name, signature);
        }
    }

    pub fn install_module_intrinsic_functions(
        &mut self,
        functions: &BTreeMap<String, HirIntrinsicFunction<'ta>>,
    ) {
        for (name, fun) in functions.iter() {
            self.functions.insert(name.to_owned(), fun.signature());
        }
    }

    pub fn install_module_intrinsic_scalars(
        &mut self,
        scalars: &BTreeMap<String, HirIntrinsicScalar<'ta>>,
    ) {
        for (name, scalar) in scalars.iter() {
            self.scalar_types.insert(name.to_owned(), scalar.clone());
        }
    }
}

pub struct HirModuleTypeCheckerPass();

impl HirModuleTypeCheckerPass {
    /// Type-check and perform type inference on the given module.
    pub fn visit<'ta>(module: &mut HirModule<'ta>, cx: &mut TypingContext<'ta>) -> HirResult<()> {
        cx.locals.enter_scope();
        cx.install_module_records(&module.records);
        cx.install_module_functions(&module.functions);
        cx.install_module_intrinsic_functions(&module.intrinsic_functions);
        cx.install_module_intrinsic_scalars(&module.intrinsic_scalars);

        Self::visit_module_functions(cx, &mut module.functions)?;
        Self::visit_module_intrinsic_functions(cx, &mut module.intrinsic_functions)?;
        Self::visit_module_records(cx, &mut module.records)?;
        cx.locals.leave_scope();
        Ok(())
    }

    pub fn visit_module_functions<'ta>(
        cx: &mut TypingContext<'ta>,
        functions: &mut BTreeMap<String, HirFunction<'ta>>,
    ) -> HirResult<()> {
        for fun in functions.values_mut() {
            Self::visit_function(cx, fun)?;
        }
        Ok(())
    }

    pub fn visit_module_intrinsic_functions<'ta>(
        cx: &mut TypingContext<'ta>,
        functions: &mut BTreeMap<String, HirIntrinsicFunction<'ta>>,
    ) -> HirResult<()> {
        for fun in functions.values_mut() {
            Self::visit_intrinsic_function(cx, fun)?;
        }
        Ok(())
    }

    pub fn visit_module_records<'ta>(
        cx: &mut TypingContext<'ta>,
        records: &mut BTreeMap<String, HirRecord<'ta>>,
    ) -> HirResult<()> {
        for rec in records.values_mut() {
            Self::visit_hir_record(cx, rec)?;
        }
        Ok(())
    }

    /// Traverse the intrinsic function.
    ///
    /// Intrinsic functions only require that their types are defined. Because type parameters
    /// passed to intrinsic functions are erased, we don't need to worry about them. The compiler
    /// assumes that the intrinsic functions are correct.
    ///
    /// TODO: If we wish to support extern "C" signatures, we should type check them here.
    pub fn visit_intrinsic_function<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirIntrinsicFunction<'ta>,
    ) -> HirResult<()> {
        cx.local_type_parameter_substitutions.enter_scope();
        for type_parameter in node.type_parameters.iter() {
            let substitution = cx.fresh_type_variable();
            cx.substitutions.push(substitution);
            cx.local_type_parameter_substitutions
                .add(&type_parameter.syntax_name.name, substitution);
        }
        node.return_type = Self::visit_type(cx, node.return_type)?;
        for p in node.parameters.iter_mut() {
            p.r#type = Self::visit_type(cx, p.r#type)?;
        }
        cx.local_type_parameter_substitutions.leave_scope();
        Ok(())
    }

    /// Traverse the function.
    ///
    /// This ensures the types of the function's parameters and return type are correct, then it
    /// recurses down into the function body.
    pub fn visit_function<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirFunction<'ta>,
    ) -> HirResult<()> {
        // Create substitutions for all the type parameters.
        cx.local_type_parameter_substitutions.enter_scope();
        for type_parameter in node.type_parameters.iter() {
            let substitution = cx.fresh_type_variable();
            cx.substitutions.push(substitution);
            cx.local_type_parameter_substitutions
                .add(&type_parameter.syntax_name.name, substitution);
        }
        node.return_type = Self::visit_type(cx, node.return_type)?;
        // Push the function's type onto the current stack, so that return statements can be checked
        // against the expected return type.
        let HirTy::Function(self_ty) = cx.arena.get_function_ty(
            node.return_type,
            node.parameters.iter().map(|p| p.r#type).collect(),
        ) else {
            ice!("freshly built function type should be a function");
        };
        cx.current_function.push_back(self_ty);
        cx.locals.enter_scope();
        // Push all the function parameters into the local context.
        for p in node.parameters.iter_mut() {
            p.r#type = Self::visit_type(cx, p.r#type)?;
            cx.locals.add(&p.name.name, p.r#type);
        }
        // Recurse down into the body.
        for stmt in node.body.iter_mut() {
            Self::visit_stmt(cx, stmt)?;
        }

        cx.locals.leave_scope();
        cx.local_type_parameter_substitutions.leave_scope();
        // All the substitutions should have been drained by this point.
        // assert_eq!(cx.substitutions.len(), 0);
        Ok(())
    }

    /// Visit a record.
    ///
    /// This ensures that all the record fields are valid, and that the record is not recursive.
    ///
    /// A record type is infinitely recursive if any of its fields are unable to break the cycle.
    /// Types that can be break the cycle are pointer types. This means that if a type directly
    /// references itself by name
    pub fn visit_hir_record<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirRecord<'ta>,
    ) -> HirResult<()> {
        for field in node.fields.values_mut() {
            field.r#type = Self::visit_type(cx, field.r#type)?;
            // Check if the field directly references itself
            let is_directly_self_referential =
                matches!(field.r#type, HirTy::Nominal(n) if n.name.name == node.name.name);
            if is_directly_self_referential {
                return Err(HirError::TypeFieldInfiniteRecursion(
                    TypeFieldInfiniteRecursionError {
                        type_name: node.name.name.to_owned(),
                        offending_field: field.name.name.to_owned(),
                        span: field.span.clone(),
                    },
                ));
            }
        }
        Ok(())
    }

    /// Visit a type.
    ///
    /// This ensures that the type is well-formed, and that it is not infinitely recursive.
    ///
    /// Because all uninitialized types are eliminated during type inference, we must replace all
    /// uninitialized types with fresh type variables here.
    pub fn visit_type<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &'ta HirTy<'ta>,
    ) -> HirResult<&'ta HirTy<'ta>> {
        match node {
            t @ HirTy::Nominal(_) => Self::visit_nominal_ty(cx, t),
            HirTy::Function(t) => Self::visit_function_ty(cx, t),
            HirTy::Pointer(t) => Self::visit_pointer_ty(cx, t),
            t @ HirTy::Variable(_)
            | t @ HirTy::Integer32(_)
            | t @ HirTy::Boolean(_)
            | t @ HirTy::Unit(_) => Ok(node),
            // If the type was uninitialized by the lowering pass, we need to replace it with a
            // fresh type variable here.
            HirTy::Uninitialized(_) => {
                let v = cx.fresh_type_variable();
                Ok(v)
            }
        }
    }

    /// A named type is either a user-defined record, a builtin type, or a generic type parameter.
    ///
    /// If it is a generic type parameter, we substitute it with the matching substitution from the
    /// local type parameter substitution context.
    ///
    /// It is important that we check for local type parameter substitutions first, as they can
    /// shadow global names.
    pub fn visit_nominal_ty<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &'ta HirTy<'ta>,
    ) -> HirResult<&'ta HirTy<'ta>> {
        let HirTy::Nominal(n) = node else {
            ice!("visit_nominal_ty called with non-nominal type");
        };
        if let Some(sub) = cx.local_type_parameter_substitutions.find(&n.name.name) {
            return Ok(sub);
        }
        // Check if the name is a builtin or record type.
        if cx.scalar_types.contains_key(&n.name.name) {
            return Ok(node);
        }
        if cx.record_types.contains_key(&n.name.name) {
            return Ok(node);
        }
        Err(HirError::UnknownType(UnknownTypeError {
            name: n.name.name.to_owned(),
            span: n.name.span.clone(),
        }))
    }

    /// Visit a function type.
    pub fn visit_function_ty<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &HirFunctionTy<'ta>,
    ) -> HirResult<&'ta HirTy<'ta>> {
        let parameters = node
            .parameters
            .iter()
            .map(|p| Self::visit_type(cx, p))
            .collect::<HirResult<Vec<_>>>()?;
        let return_type = Self::visit_type(cx, node.return_type)?;
        Ok(cx.arena.get_function_ty(return_type, parameters))
    }

    /// Visit a pointer type.
    pub fn visit_pointer_ty<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &'ta HirPointerTy<'ta>,
    ) -> HirResult<&'ta HirTy<'ta>> {
        let inner = Self::visit_type(cx, node.inner)?;
        Ok(cx.arena.get_pointer_ty(inner))
    }

    /// Visit an expression and infer its type.
    pub fn visit_expr<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirExpr<'ta>) -> HirResult<()> {
        match node {
            e @ HirExpr::IntegerLiteral(_) => Self::visit_integer_literal_expr(cx, e),
            e @ HirExpr::BooleanLiteral(_) => Self::visit_boolean_literal_expr(cx, e),
            e @ HirExpr::Group(_) => Self::visit_group_expr(cx, e),
            e @ HirExpr::Reference(_) => Self::visit_reference_expr(cx, e),
            e @ HirExpr::Assign(_) => Self::visit_assign_expr(cx, e),
            e @ HirExpr::OffsetIndex(_) => Self::visit_offset_index_expr(cx, e),
            e @ HirExpr::ConstantIndex(_) => Self::visit_constant_index_expr(cx, e),
            e @ HirExpr::Call(_) => Self::visit_call_expr(cx, e),
            e @ HirExpr::Construct(_) => Self::visit_construct_expr(cx, e),
            e @ HirExpr::AddressOf(_) => Self::visit_address_of_expr(cx, e),
            e @ HirExpr::Deref(_) => Self::visit_deref_expr(cx, e),
            e @ HirExpr::UnaryOp(_) => todo!(),
            e @ HirExpr::BinaryOp(_) => todo!(),
        }
    }

    /// Visit an integer literal expression.
    ///
    /// The integer literal expression's type is always the integer32 type.
    pub fn visit_integer_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::IntegerLiteral(e) = node else {
            ice!("visit_integer_literal_expr called with non-integer literal");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    /// Visit a boolean literal expression.
    ///
    /// The boolean literal expression's is always the boolean type.
    pub fn visit_boolean_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::BooleanLiteral(e) = node else {
            ice!("visit_boolean_literal_expr called with non-boolean literal");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    /// Visit a group expression.
    ///
    /// The grouping expression's type is inferred from the inner expression.
    pub fn visit_group_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Group(e) = node else {
            ice!("visit_group_expr called with non-group expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    /// Visit a reference expression.
    ///
    /// For a reference expression, we get the local type from the local context, and infer the
    /// type according to that type.
    pub fn visit_reference_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Reference(e) = node else {
            ice!("visit_reference_expr called with non-reference expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        // See if the name resolves to a local let-binding or a function name.
        if cx.locals.find(&e.name.name).is_none() && !cx.functions.contains_key(&e.name.name) {
            return Err(HirError::InvalidReference(InvalidReferenceError {
                name: e.name.name.to_owned(),
                span: e.span.clone(),
            }));
        }
        cx.infer(node, node.ty())?;
        Ok(())
    }

    /// Visit an assign expression.
    ///
    /// In order to prevent chaining of assignment such as `a = b = c`, we simply infer the type of
    /// the entire expression to be void.
    pub fn visit_assign_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Assign(e) = node else {
            ice!("visit_assign_expr called with non-assign expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.lhs)?;
        Self::visit_expr(cx, &mut e.rhs)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_offset_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::OffsetIndex(e) = node else {
            ice!("visit_offset_index_expr called with non-offset index expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.origin)?;
        Self::visit_expr(cx, &mut e.index)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_constant_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::ConstantIndex(e) = node else {
            ice!("visit_constant_index_expr called with non-constant index expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.origin)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_call_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Call(e) = node else {
            ice!("visit_call_expr called with non-call expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.callee)?;
        for arg in e.arguments.iter_mut() {
            Self::visit_expr(cx, arg)?;
        }
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_construct_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Construct(e) = node else {
            ice!("visit_construct_expr called with non-construct expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        for arg in e.arguments.iter_mut() {
            Self::visit_expr(cx, &mut arg.expr)?;
        }
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_address_of_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::AddressOf(e) = node else {
            ice!("visit_address_of_expr called with non-address of expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    pub fn visit_deref_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Deref(e) = node else {
            ice!("visit_deref_expr called with non-deref expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty())?;
        Ok(())
    }

    /// Visit a statement.
    pub fn visit_stmt<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirStmt<'ta>) -> HirResult<()> {
        match node {
            HirStmt::Let(s) => Self::visit_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::visit_expr_stmt(cx, e),
            HirStmt::Loop(_) => todo!(),
            HirStmt::Return(_) => Ok(()),
            HirStmt::If(_) => todo!(),
            HirStmt::Break(_) => todo!(),
            HirStmt::Continue(_) => todo!(),
            HirStmt::Block(_) => todo!(),
        }
    }

    /// Visit a let statement.
    ///
    /// When visiting a let binding, we first visit the type to replace any uninitialized types
    /// with a fresh type variable, then we update the type environment with the new type.
    pub fn visit_let_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirLetStmt<'ta>,
    ) -> HirResult<()> {
        // This coalesces let statements without a type annotation into a type variable.
        node.r#type = Self::visit_type(cx, node.r#type)?;
        Self::visit_expr(cx, &mut node.value)?;
        cx.infer(&mut node.value, node.r#type)?;
        cx.solve_constraints()?;
        node.r#type = cx.substitute(node.r#type)?;
        cx.substitute_expr(&mut node.value)?;
        cx.locals.add(&node.name.name, node.r#type);
        Ok(())
    }

    pub fn visit_expr_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExprStmt<'ta>,
    ) -> HirResult<()> {
        Self::visit_expr(cx, &mut node.expr)?;
        cx.solve_constraints()?;
        cx.substitute_expr(&mut node.expr)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {}
