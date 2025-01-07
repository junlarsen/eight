use crate::context::LocalContext;
use crate::error::{
    FunctionTypeMismatchError, HirError, HirResult, InvalidFieldReferenceOfNonStructError,
    InvalidReferenceError, InvalidStructFieldReferenceError, MissingFieldError,
    SelfReferentialTypeError, TypeFieldInfiniteRecursionError, TypeMismatchError,
    UnknownFieldError, UnknownTypeError,
};
use crate::expr::HirExpr;
use crate::fun::{HirFunction, HirFunctionSignature, HirIntrinsicFunction};
use crate::rec::HirRecord;
use crate::scalar::HirIntrinsicScalar;
use crate::stmt::{
    HirBlockStmt, HirExprStmt, HirIfStmt, HirLetStmt, HirLoopStmt, HirReturnStmt, HirStmt,
};
use crate::ty::{HirArena, HirFunctionTy, HirPointerTy, HirTy};
use crate::{HirModule, HirName};
use hachi_diagnostics::ice;
use hachi_span::Span;
use std::collections::{BTreeMap, HashSet, VecDeque};

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
    arena: &'ta HirArena<'ta>,
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
    pub fn new(arena: &'ta HirArena<'ta>) -> Self {
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
        ty: &'ta HirTy<'ta>,
        field: HirName,
        inner: &'ta HirTy<'ta>,
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
                            span: field.span,
                        },
                    ));
                };
                let constraint = EqualityConstraint {
                    expected: record_field.r#type,
                    expected_loc: record_field.span,
                    actual_loc: n.name.span,
                    actual: resolved_type,
                };
                self.unify_eq(constraint)?;
                Ok(())
            }
            _ => Err(HirError::InvalidFieldReferenceOfNonStruct(
                InvalidFieldReferenceOfNonStructError {
                    ty: format!("{}", resolved_type),
                    name: field.name.to_owned(),
                    span: field.span,
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
                    expected_loc,
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
                        expected: parameter,
                        expected_loc,
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

    /// Perform type inference on an expression.
    ///
    /// Expression types have their types set as uninitialized after the AST syntax lowering pass.
    /// This means that its up to the inference engine to determine the type of the expression.
    ///
    /// Effectively, the expression type here will always be a fresh type variable.
    pub fn infer_expr(&mut self, expr: &mut HirExpr<'ta>) -> HirResult<()> {
        self.infer(expr, expr.ty())?;
        Ok(())
    }

    /// Infer the expression's type based on its expected type.
    ///
    /// This collects the necessary constraints on the expression's type based on its structure. The
    /// constraints are solved in a post-order traversal of the expression tree once all the
    /// constraints of the current node and its children have been collected.
    pub fn infer(
        &mut self,
        expr: &mut HirExpr<'ta>,
        expected_ty: &'ta HirTy<'ta>,
    ) -> HirResult<()> {
        match expr {
            // Integer literals are always i32 at the moment
            HirExpr::IntegerLiteral(e) => {
                self.constrain_eq(expected_ty, self.arena.get_integer32_ty(), e.span, e.span);
                Ok(())
            }
            // Booleans always have the bool type
            HirExpr::BooleanLiteral(e) => {
                self.constrain_eq(expected_ty, self.arena.get_boolean_ty(), e.span, e.span);
                Ok(())
            }
            // We don't want assignments to be chained, so we infer them as unit
            HirExpr::Assign(e) => {
                self.constrain_eq(expected_ty, self.arena.get_unit_ty(), e.span, *e.lhs.span());
                Ok(())
            }
            HirExpr::Reference(e) => {
                // We attempt to look up a local variable first. This is cheaper than attempting to
                // instantiate a generic function.
                if let Some(local_ty) = self.locals.find(&e.name.name) {
                    self.constrain_eq(expected_ty, local_ty, e.span, e.name.span);
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
                    self.constrain_eq(expected_ty, ty, e.span, e.name.span);
                    return Ok(());
                }

                // Otherwise, we need to instantiate the generic parameters of the function, and
                // substitute the parameters and return types if they refer to one of the generic
                // type parameters.
                // TODO: Prevent this clone
                let signature = signature.clone();
                self.local_type_parameter_substitutions.enter_scope();
                for type_parameter in signature.type_parameters.iter() {
                    let ty = self.fresh_type_variable();
                    self.local_type_parameter_substitutions
                        .add(&type_parameter.syntax_name.name, ty);
                }
                // The types of the signature can refer to the type parameters at arbitrary depths,
                // e.g. `**T`, so we just recurse down to substitute.
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|p| HirModuleTypeCheckerPass::visit_type(self, p.r#type))
                    .collect::<HirResult<Vec<_>>>()?;
                let return_type =
                    HirModuleTypeCheckerPass::visit_type(self, signature.return_type)?;
                let ty = self.arena.get_function_ty(return_type, parameters);
                self.constrain_eq(expected_ty, ty, e.span, e.name.span);
                Ok(())
            }
            HirExpr::OffsetIndex(e) => {
                // The index must be an integer type
                self.constrain_eq(
                    self.arena.get_integer32_ty(),
                    e.index.ty(),
                    e.span,
                    *e.index.span(),
                );
                // The origin must be a pointer of the element type
                let elem_ptr_ty = self.arena.get_pointer_ty(expected_ty);
                self.constrain_eq(elem_ptr_ty, e.origin.ty(), e.span, *e.origin.span());
                // The resulting type must be the element type
                self.constrain_eq(expected_ty, e.ty, e.span, *e.origin.span());
                Ok(())
            }
            HirExpr::ConstantIndex(e) => {
                self.constrain_eq(expected_ty, e.ty, e.span, *e.origin.span());
                self.constrain_field_projection(e.origin.ty(), e.index.clone(), expected_ty);
                Ok(())
            }
            HirExpr::Call(e) => {
                let expected_args = e.arguments.iter().map(|a| a.ty()).collect::<Vec<_>>();
                let expected_signature = self.arena.get_function_ty(expected_ty, expected_args);
                self.unify_eq(EqualityConstraint {
                    expected: expected_signature,
                    actual: e.callee.ty(),
                    expected_loc: e.span,
                    actual_loc: *e.callee.span(),
                })?;

                // Constrain the return type of the expression to the wanted type
                self.unify_eq(EqualityConstraint {
                    expected: expected_ty,
                    actual: e.ty,
                    expected_loc: e.span,
                    actual_loc: *e.callee.span(),
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
                let mut visited_fields = HashSet::new();
                for provided_field in e.arguments.iter() {
                    let Some(field_definition) = ty.fields.get(&provided_field.field.name) else {
                        return Err(HirError::UnknownField(UnknownFieldError {
                            field_name: provided_field.field.name.to_owned(),
                            type_name: n.name.name.to_owned(),
                            span: provided_field.field.span,
                        }));
                    };
                    visited_fields.insert(provided_field.field.name.clone());
                    self.unify_eq(EqualityConstraint {
                        actual: provided_field.expr.ty(),
                        actual_loc: *provided_field.expr.span(),
                        expected: field_definition.r#type,
                        expected_loc: field_definition.span,
                    })?;
                }
                // If some of the fields from the struct are missing
                for field in ty.fields.values() {
                    if !visited_fields.contains(&field.name.name) {
                        return Err(HirError::MissingField(MissingFieldError {
                            type_name: n.name.name.to_owned(),
                            field_name: field.name.name.to_owned(),
                            span: e.span,
                            defined_at: field.span,
                        }));
                    }
                }
                // Constrain the expected type to the callee type, and the callee to the type being
                // constructed.
                self.unify_eq(EqualityConstraint {
                    expected: e.ty,
                    expected_loc: e.span,
                    actual: e.callee,
                    actual_loc: e.span,
                })?;
                self.unify_eq(EqualityConstraint {
                    expected: e.ty,
                    expected_loc: e.span,
                    actual: expected_ty,
                    actual_loc: e.span,
                })?;
                Ok(())
            }
            HirExpr::AddressOf(e) => {
                // &a means that e is *inner, and expected_ty is *inner
                let result_ty = self.arena.get_pointer_ty(e.inner.ty());
                self.constrain_eq(expected_ty, result_ty, e.span, *e.inner.span());
                self.constrain_eq(e.ty, result_ty, e.span, *e.inner.span());
                Ok(())
            }
            HirExpr::Deref(e) => {
                // *a means inner is a pointer type, and expected and e are unbox inner
                let inner_ptr = self.arena.get_pointer_ty(expected_ty);
                self.constrain_eq(e.inner.ty(), inner_ptr, e.span, *e.inner.span());
                self.constrain_eq(e.ty, expected_ty, e.span, *e.inner.span());
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

    /// Perform the substitution step for a given type.
    ///
    /// This function substitutes any type variables in the given type with the matching type in the
    /// local substitution set $T, as long as the type variable is not equal to $T.
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
                // that we may have a substitution for. e.g, $0 => $1 => i32
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
    /// Copy the records frs from the given module into the context.
    pub fn install_module_records(&mut self, records: &BTreeMap<String, HirRecord<'ta>>) {
        for rec in records.values() {
            self.record_types
                .insert(rec.name.name.to_owned(), rec.clone());
        }
    }

    /// Copy the functions from the given module into the context.
    pub fn install_module_functions(&mut self, functions: &BTreeMap<String, HirFunction<'ta>>) {
        let signatures = functions
            .iter()
            .map(|(name, fun)| (name.to_owned(), fun.signature()));
        for (name, signature) in signatures {
            self.functions.insert(name, signature);
        }
    }

    /// Copy the intrinsic functions from the given module into the context.
    pub fn install_module_intrinsic_functions(
        &mut self,
        functions: &BTreeMap<String, HirIntrinsicFunction<'ta>>,
    ) {
        for (name, fun) in functions.iter() {
            self.functions.insert(name.to_owned(), fun.signature());
        }
    }

    /// Copy the intrinsic scalars from the given module into the context.
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

    /// Traverse the functions in the given module.
    pub fn visit_module_functions<'ta>(
        cx: &mut TypingContext<'ta>,
        functions: &mut BTreeMap<String, HirFunction<'ta>>,
    ) -> HirResult<()> {
        for fun in functions.values_mut() {
            Self::visit_function(cx, fun)?;
        }
        Ok(())
    }

    /// Traverse the intrinsic functions in the given module.
    pub fn visit_module_intrinsic_functions<'ta>(
        cx: &mut TypingContext<'ta>,
        functions: &mut BTreeMap<String, HirIntrinsicFunction<'ta>>,
    ) -> HirResult<()> {
        for fun in functions.values_mut() {
            Self::visit_intrinsic_function(cx, fun)?;
        }
        Ok(())
    }

    /// Traverse the records in the given module.
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
    /// Right now the compiler just assumes that the intrinsic functions are correct.
    pub fn visit_intrinsic_function<'ta>(
        _: &mut TypingContext<'ta>,
        _: &mut HirIntrinsicFunction<'ta>,
    ) -> HirResult<()> {
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
        for type_parameter in node.type_parameters.iter_mut() {
            let substitution = cx.fresh_type_variable();
            // This is only cosmetic so that the debug pass can print the type parameter names with
            // their substitutions. It is not used in the type checker.
            type_parameter.substitution_name = Some(substitution);
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
        cx.local_type_parameter_substitutions.leave_scope();
        cx.substitutions.clear();

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
                        span: field.span,
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
            span: n.name.span,
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

    /// Collect type constraints for an expression.
    pub fn enter_expr<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirExpr<'ta>) -> HirResult<()> {
        match node {
            e @ HirExpr::IntegerLiteral(_) => Self::enter_integer_literal_expr(cx, e),
            e @ HirExpr::BooleanLiteral(_) => Self::enter_boolean_literal_expr(cx, e),
            e @ HirExpr::Group(_) => Self::enter_group_expr(cx, e),
            e @ HirExpr::Reference(_) => Self::enter_reference_expr(cx, e),
            e @ HirExpr::Assign(_) => Self::enter_assign_expr(cx, e),
            e @ HirExpr::OffsetIndex(_) => Self::enter_offset_index_expr(cx, e),
            e @ HirExpr::ConstantIndex(_) => Self::enter_constant_index_expr(cx, e),
            e @ HirExpr::Call(_) => Self::enter_call_expr(cx, e),
            e @ HirExpr::Construct(_) => Self::enter_construct_expr(cx, e),
            e @ HirExpr::AddressOf(_) => Self::enter_address_of_expr(cx, e),
            e @ HirExpr::Deref(_) => Self::enter_deref_expr(cx, e),
            e @ HirExpr::UnaryOp(_) => todo!(),
            e @ HirExpr::BinaryOp(_) => todo!(),
        }
    }

    /// Perform substitution for an expression.
    pub fn leave_expr<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirExpr<'ta>) -> HirResult<()> {
        match node {
            e @ HirExpr::IntegerLiteral(_) => Self::leave_integer_literal_expr(cx, e),
            e @ HirExpr::BooleanLiteral(_) => Self::leave_boolean_literal_expr(cx, e),
            e @ HirExpr::Group(_) => Self::leave_group_expr(cx, e),
            e @ HirExpr::Reference(_) => Self::leave_reference_expr(cx, e),
            e @ HirExpr::Assign(_) => Self::leave_assign_expr(cx, e),
            e @ HirExpr::OffsetIndex(_) => Self::leave_offset_index_expr(cx, e),
            e @ HirExpr::ConstantIndex(_) => Self::leave_constant_index_expr(cx, e),
            e @ HirExpr::Call(_) => Self::leave_call_expr(cx, e),
            e @ HirExpr::Construct(_) => Self::leave_construct_expr(cx, e),
            e @ HirExpr::AddressOf(_) => Self::leave_address_of_expr(cx, e),
            e @ HirExpr::Deref(_) => Self::leave_deref_expr(cx, e),
            e @ HirExpr::UnaryOp(_) => todo!(),
            e @ HirExpr::BinaryOp(_) => todo!(),
        }
    }

    /// Collect type constraints for an integer literal expression.
    ///
    /// Inference ensures that the integer literal is tied to the i32 type.
    pub fn enter_integer_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::IntegerLiteral(e) = node else {
            ice!("visit_integer_literal_expr called with non-integer literal");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for an integer literal expression.
    pub fn leave_integer_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::IntegerLiteral(e) = node else {
            ice!("visit_integer_literal_expr called with non-integer literal");
        };
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a boolean literal expression.
    ///
    /// [`infer_expr`] ensures that the boolean literal is tied to the boolean type.
    pub fn enter_boolean_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::BooleanLiteral(e) = node else {
            ice!("visit_boolean_literal_expr called with non-boolean literal");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a boolean literal expression.
    pub fn leave_boolean_literal_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::BooleanLiteral(e) = node else {
            ice!("visit_boolean_literal_expr called with non-boolean literal");
        };
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a group expression.
    ///
    /// The grouping expression's type is inferred from the inner expression.
    pub fn enter_group_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Group(e) = node else {
            ice!("visit_group_expr called with non-group expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.inner)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a group expression.
    pub fn leave_group_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Group(e) = node else {
            ice!("visit_group_expr called with non-group expression");
        };
        Self::leave_expr(cx, &mut e.inner)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a reference expression.
    ///
    /// For a reference expression, we constrain it to the type of the local variable in the local
    /// context.
    ///
    /// This function also performs validation on the local lookup.
    pub fn enter_reference_expr<'ta>(
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
                span: e.span,
            }));
        }
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a reference expression.
    pub fn leave_reference_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Reference(e) = node else {
            ice!("visit_reference_expr called with non-reference expression");
        };
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for an assign expression.
    ///
    /// In order to prevent chaining of assignment such as `a = b = c`, we simply infer the type of
    /// the entire expression to be void.
    pub fn enter_assign_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Assign(e) = node else {
            ice!("visit_assign_expr called with non-assign expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.lhs)?;
        Self::enter_expr(cx, &mut e.rhs)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    pub fn leave_assign_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Assign(e) = node else {
            ice!("visit_assign_expr called with non-assign expression");
        };
        Self::leave_expr(cx, &mut e.lhs)?;
        Self::leave_expr(cx, &mut e.rhs)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for an offset index expression.
    ///
    /// Since offsets only work on pointer types, infer will constrain the origin to be a pointer,
    /// and the index to be an integer.
    pub fn enter_offset_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::OffsetIndex(e) = node else {
            ice!("visit_offset_index_expr called with non-offset index expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.origin)?;
        Self::enter_expr(cx, &mut e.index)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for an offset index expression.
    pub fn leave_offset_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::OffsetIndex(e) = node else {
            ice!("visit_offset_index_expr called with non-offset index expression");
        };
        Self::leave_expr(cx, &mut e.origin)?;
        Self::leave_expr(cx, &mut e.index)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a constant index expression.
    pub fn enter_constant_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::ConstantIndex(e) = node else {
            ice!("visit_constant_index_expr called with non-constant index expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.origin)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a constant index expression.
    pub fn leave_constant_index_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::ConstantIndex(e) = node else {
            ice!("visit_constant_index_expr called with non-constant index expression");
        };
        Self::leave_expr(cx, &mut e.origin)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a call expression.
    pub fn enter_call_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Call(e) = node else {
            ice!("visit_call_expr called with non-call expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.callee)?;
        for arg in e.arguments.iter_mut() {
            Self::enter_expr(cx, arg)?;
        }
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a call expression.
    pub fn leave_call_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Call(e) = node else {
            ice!("visit_call_expr called with non-call expression");
        };
        Self::leave_expr(cx, &mut e.callee)?;
        for arg in e.arguments.iter_mut() {
            Self::leave_expr(cx, arg)?;
        }
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a construct expression.
    pub fn enter_construct_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Construct(e) = node else {
            ice!("visit_construct_expr called with non-construct expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        for arg in e.arguments.iter_mut() {
            Self::enter_expr(cx, &mut arg.expr)?;
        }
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a construct expression.
    pub fn leave_construct_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Construct(e) = node else {
            ice!("visit_construct_expr called with non-construct expression");
        };
        e.ty = cx.substitute(e.ty)?;
        for arg in e.arguments.iter_mut() {
            Self::leave_expr(cx, &mut arg.expr)?;
        }
        Ok(())
    }

    /// Collect type constraints for an address of expression.
    pub fn enter_address_of_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::AddressOf(e) = node else {
            ice!("visit_address_of_expr called with non-address of expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.inner)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for an address of expression.
    pub fn leave_address_of_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::AddressOf(e) = node else {
            ice!("visit_address_of_expr called with non-address of expression");
        };
        Self::leave_expr(cx, &mut e.inner)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a deref expression.
    pub fn enter_deref_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Deref(e) = node else {
            ice!("visit_deref_expr called with non-deref expression");
        };
        e.ty = Self::visit_type(cx, e.ty)?;
        Self::enter_expr(cx, &mut e.inner)?;
        cx.infer_expr(node)?;
        Ok(())
    }

    /// Perform substitution for a deref expression.
    pub fn leave_deref_expr<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExpr<'ta>,
    ) -> HirResult<()> {
        let HirExpr::Deref(e) = node else {
            ice!("visit_deref_expr called with non-deref expression");
        };
        Self::leave_expr(cx, &mut e.inner)?;
        e.ty = cx.substitute(e.ty)?;
        Ok(())
    }

    /// Collect type constraints for a statement.
    ///
    /// This function is responsible for collecting constraints for all the expressions in children
    /// of the node.
    ///
    /// In a second pass, we will perform substitution on the same expressions, after all the
    /// constraints have been collected.
    pub fn enter_stmt<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirStmt<'ta>) -> HirResult<()> {
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
    pub fn leave_stmt<'ta>(cx: &mut TypingContext<'ta>, node: &mut HirStmt<'ta>) -> HirResult<()> {
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
    pub fn enter_let_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirLetStmt<'ta>,
    ) -> HirResult<()> {
        // Replace any uninitialized types with a fresh type variable.
        node.r#type = Self::visit_type(cx, node.r#type)?;
        Self::enter_expr(cx, &mut node.value)?;
        cx.infer(&mut node.value, node.r#type)?;
        // Propagate the type of the expression to the type of the let-binding
        node.r#type = node.value.ty();
        cx.locals.add(&node.name.name, node.r#type);
        Ok(())
    }

    /// Perform substitution for a let statement.
    pub fn leave_let_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirLetStmt<'ta>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.value)?;
        // Propagate the type of the expression to the type of the let-binding
        node.r#type = node.value.ty();
        Ok(())
    }

    /// Collect type constraints for an expression statement.
    pub fn enter_expr_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExprStmt<'ta>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.expr)?;
        Ok(())
    }

    /// Perform substitution for an expression statement.
    pub fn leave_expr_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirExprStmt<'ta>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.expr)?;
        Ok(())
    }

    /// Collect type constraints for a loop statement.
    pub fn enter_loop_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirLoopStmt<'ta>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.condition)?;
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.arena.get_boolean_ty())?;
        cx.locals.enter_scope();
        for stmt in node.body.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();
        Ok(())
    }

    /// Perform substitution for a loop statement.
    pub fn leave_loop_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirLoopStmt<'ta>,
    ) -> HirResult<()> {
        Self::leave_expr(cx, &mut node.condition)?;
        for stmt in node.body.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        Ok(())
    }

    /// Collect type constraints for a block statement.
    pub fn enter_block_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirBlockStmt<'ta>,
    ) -> HirResult<()> {
        cx.locals.enter_scope();
        for stmt in node.body.iter_mut() {
            Self::enter_stmt(cx, stmt)?;
        }
        cx.locals.leave_scope();
        Ok(())
    }

    /// Perform substitution for a block statement.
    pub fn leave_block_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirBlockStmt<'ta>,
    ) -> HirResult<()> {
        for stmt in node.body.iter_mut() {
            Self::leave_stmt(cx, stmt)?;
        }
        Ok(())
    }

    /// Collect type constraints for a break statement.
    pub fn enter_return_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirReturnStmt<'ta>,
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
    pub fn leave_return_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirReturnStmt<'ta>,
    ) -> HirResult<()> {
        if let Some(inner) = node.value.as_mut() {
            Self::leave_expr(cx, inner)?;
        }
        Ok(())
    }

    /// Collect type constraints for an if statement.
    pub fn enter_if_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirIfStmt<'ta>,
    ) -> HirResult<()> {
        Self::enter_expr(cx, &mut node.condition)?;
        // We also impose a new constraint that the condition must be a boolean
        cx.infer(&mut node.condition, cx.arena.get_boolean_ty())?;

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

    pub fn leave_if_stmt<'ta>(
        cx: &mut TypingContext<'ta>,
        node: &mut HirIfStmt<'ta>,
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
