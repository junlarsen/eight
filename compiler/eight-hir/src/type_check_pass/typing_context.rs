use crate::arena::HirArena;
use eight_middle::context::LocalContext;
use crate::error::{
    BindingReDeclaresName, ConstructingNonStructTypeError, ConstructingPointerTypeError,
    FunctionTypeMismatchError, HirError, HirResult, InvalidFieldReferenceOfNonStructError,
    InvalidStructFieldReferenceError, MissingFieldError, SelfReferentialTypeError,
    TraitDoesNotExistError, TraitInstanceMissingFnError, TraitMissingInstanceError,
    TypeMismatchError, TypeParameterShadowsExisting, UnknownFieldError,
};
use crate::expr::{
    HirAddressOfExpr, HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirDerefExpr, HirExpr, HirGroupExpr,
    HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp, HirUnaryOpExpr,
};
use crate::query::HirSignatureQueryDatabase;
use crate::ty::{HirFunctionTy, HirMetaTy, HirTy};
use crate::type_check_pass::{
    Constraint, EqualityConstraint, FieldProjectionConstraint, InstanceConstraint,
};
use eight_diagnostics::ice;
use eight_span::Span;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;

/// A context object for the type checker.
///
/// This object represents the state of the type checker.
pub struct TypingContext<'hir> {
    /// A reference to the Hir arena for allocating types.
    ///
    /// TODO: Should this be private?
    pub arena: &'hir HirArena<'hir>,
    pub module_query_db: &'hir HirSignatureQueryDatabase<'hir>,

    /// Collected constraints during inference, to be solved during unification.
    constraints: Vec<Constraint<'hir>>,
    substitutions: Vec<&'hir HirTy<'hir>>,

    /// Type parameters that are currently being substituted in the current function.
    ///
    /// This is required when traversing function bodies, as we need to substitute `let x: T = 1;`
    /// with a matching type variable from the function's signature.
    ///
    /// We currently don't support nested functions or lambdas, so this does not necessarily have to
    /// be a VecDeque, but it's here for future use.
    type_binding_context: LocalContext<&'hir str, &'hir HirTy<'hir>>,
    let_binding_context: LocalContext<&'hir str, &'hir HirTy<'hir>>,
    pub(crate) type_parameter_instantiations: LocalContext<(u32, u32), &'hir HirTy<'hir>>,
    /// Track the current function for type checking against expected return types.
    current_function: VecDeque<&'hir HirFunctionTy<'hir>>,
}

impl<'hir> Debug for TypingContext<'hir> {
    /// Debug implementation for TypingContext skipping the arena.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypingContext")
            .field("constraints", &self.constraints)
            .field("substitutions", &self.substitutions)
            .field("let_binding_context", &self.let_binding_context)
            .field("type_binding_context", &self.type_binding_context)
            .field("current_function", &self.current_function)
            .finish()
    }
}

impl<'hir> TypingContext<'hir> {
    /// Create a new typing context given the HIR arena and module signature derived from the AST.
    pub fn new(
        arena: &'hir HirArena<'hir>,
        module_query_db: &'hir HirSignatureQueryDatabase<'hir>,
    ) -> Self {
        Self {
            arena,
            module_query_db,
            constraints: Vec::new(),
            substitutions: Vec::new(),
            let_binding_context: LocalContext::default(),
            type_binding_context: LocalContext::default(),
            type_parameter_instantiations: LocalContext::default(),
            current_function: VecDeque::new(),
        }
    }

    /// Enter a new type binding scope.
    ///
    /// This is only to be used for generic type parameter boundaries, such as entering a function
    /// with generic type parameters, or the body of a trait.
    pub fn enter_type_binding_scope(&mut self) {
        self.type_binding_context.enter_scope();
        self.type_parameter_instantiations.enter_scope();
    }

    /// Leave the current type binding scope.
    pub fn leave_type_binding_scope(&mut self) {
        self.type_parameter_instantiations.leave_scope();
        self.type_binding_context.leave_scope();
    }

    pub fn reset_substitutions(&mut self) {
        self.substitutions.clear();
    }

    pub fn instantiate_type_parameter(&mut self, ty: &'hir HirTy<'hir>) -> &'hir HirTy<'hir> {
        let HirTy::Variable(type_variable) = ty else {
            ice!("type parameter was not lowered into a variable by the lowering pass")
        };
        let substitution = self.fresh_meta_variable();
        self.type_parameter_instantiations
            .add((type_variable.depth, type_variable.index), substitution);
        substitution
    }

    /// Substitute the type binding with the given name with the given type.
    pub fn record_type_binding(
        &mut self,
        name: &'hir str,
        span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        let current_depth = self.type_binding_context.depth();
        if let Some((depth, _)) = self.type_binding_context.find_with_depth(&name) {
            if depth >= current_depth {
                return Err(HirError::TypeParameterShadowsExisting(
                    TypeParameterShadowsExisting {
                        name: name.to_owned(),
                        span,
                    },
                ));
            }
        }
        self.type_binding_context.add(name, ty);
        Ok(())
    }

    /// Substitute the let binding with the given name with the given type.
    ///
    /// Shadowing of let bindings is allowed, as long as the existing binding exists in a scope that
    /// is a parent of the current scope.
    pub fn record_let_binding(
        &mut self,
        name: &'hir str,
        span: Span,
        ty: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        let current_depth = self.let_binding_context.depth();
        if let Some((depth, _)) = self.let_binding_context.find_with_depth(&name) {
            if depth >= current_depth {
                return Err(HirError::BindingReDeclaresName(BindingReDeclaresName {
                    name: name.to_owned(),
                    span,
                }));
            }
        }
        self.let_binding_context.add(name, ty);
        Ok(())
    }

    /// Find the type of a let binding.
    pub fn find_let_binding(&self, name: &'hir str) -> Option<&'hir HirTy<'hir>> {
        self.let_binding_context.find(&name).copied()
    }

    /// Find the type of a type binding.
    pub fn find_type_binding(&self, name: &'hir str) -> Option<&'hir HirTy<'hir>> {
        self.type_binding_context.find(&name).copied()
    }

    /// Enter a new let binding scope.
    pub fn enter_let_binding_scope(&mut self) {
        self.let_binding_context.enter_scope();
    }

    /// Leave the current let binding scope.
    pub fn leave_let_binding_scope(&mut self) {
        self.let_binding_context.leave_scope();
    }

    /// Record the entry of a function.
    pub fn record_function_context_entry(&mut self, ty: &'hir HirFunctionTy<'hir>) {
        self.current_function.push_back(ty);
    }

    /// Record the exit of a function.
    pub fn record_function_context_exit(&mut self) {
        self.current_function.pop_back();
    }

    /// Find the function that is currently being visited.
    pub fn find_function_context(&self) -> Option<&'hir HirFunctionTy<'hir>> {
        self.current_function.back().copied()
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
            expr.lhs.span(),
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
        if let Some(local_ty) = self.find_let_binding(expr.name) {
            self.constrain_eq(expectation, local_ty, expr.span, expr.name_span);
            return Ok(());
        }

        // If the function refers to a function signature, we attempt to instantiate it if
        // it is generic.
        let Some(signature) = self.module_query_db.query_function_by_name(expr.name) else {
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
        let mut instantiations = HashMap::new();
        let parameters = signature
            .parameters
            .iter()
            .map(|p| self.eliminate_type_variables_within_ty(&mut instantiations, p.ty))
            .collect::<Vec<_>>();
        let return_type =
            self.eliminate_type_variables_within_ty(&mut instantiations, signature.return_type);
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
            expr.index.span(),
        );
        // The origin must be a pointer of the element type
        let elem_ptr_ty = self.arena.types().get_pointer_ty(expectation);
        self.constrain_eq(elem_ptr_ty, expr.origin.ty(), expr.span, expr.origin.span());
        // The resulting type must be the element type
        self.constrain_eq(expectation, expr.ty, expr.span, expr.origin.span());
        Ok(())
    }

    /// Infer the type of a constant index expression.
    pub fn infer_constant_index_expr(
        &mut self,
        expr: &mut HirConstantIndexExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.constrain_eq(expectation, expr.ty, expr.span, expr.origin.span());
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
            actual_loc: expr.callee.span(),
        })?;

        // Constrain the return type of the expression to the wanted type
        self.unify_eq(EqualityConstraint {
            expectation,
            actual: expr.ty,
            expectation_loc: expr.span,
            actual_loc: expr.callee.span(),
        })?;
        Ok(())
    }

    /// Infer the type of a construct expression.
    pub fn infer_construct_expr(
        &mut self,
        expr: &mut HirConstructExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        let struct_type = match expr.callee {
            HirTy::Nominal(n) => n,
            HirTy::Integer32(_) | HirTy::Boolean(_) | HirTy::Unit(_) => {
                return Err(HirError::ConstructingNonStructType(
                    ConstructingNonStructTypeError {
                        name: expr.callee.format(),
                        span: expr.span,
                    },
                ));
            }
            HirTy::Pointer(_) => {
                return Err(HirError::ConstructingPointerType(
                    ConstructingPointerTypeError {
                        name: expr.callee.format(),
                        span: expr.span,
                    },
                ));
            }
            // Function types are not first-class members at the moment.
            HirTy::Uninitialized(_) | HirTy::Variable(_) | HirTy::Function(_) => {
                ice!("called infer_construct_expr on a type that doesn't exist")
            }
            HirTy::Meta(_) => todo!("how to handle?"),
        };
        let ty = self
            .module_query_db
            .query_struct_by_name(struct_type.name)
            .unwrap_or_else(|| ice!("struct type not found"));
        let mut visited_fields = HashSet::new();
        for provided_field in expr.arguments.iter() {
            let Some(field_definition) = ty.fields.get(&provided_field.field) else {
                return Err(HirError::UnknownField(UnknownFieldError {
                    field_name: provided_field.field.to_owned(),
                    type_name: struct_type.name.to_owned(),
                    span: provided_field.field_span,
                }));
            };
            visited_fields.insert(provided_field.field);
            self.unify_eq(EqualityConstraint {
                actual: provided_field.expr.ty(),
                actual_loc: provided_field.expr.span(),
                expectation: field_definition.ty,
                expectation_loc: field_definition.span,
            })?;
        }
        // If some of the fields from the struct are missing
        for field in ty.fields.values() {
            if !visited_fields.contains(field.name) {
                return Err(HirError::MissingField(MissingFieldError {
                    type_name: struct_type.name.to_owned(),
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
        self.constrain_eq(expectation, result_ty, expr.span, expr.inner.span());
        self.constrain_eq(expr.ty, result_ty, expr.span, expr.inner.span());
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
        self.constrain_eq(expr.inner.ty(), inner_ptr, expr.span, expr.inner.span());
        self.constrain_eq(expr.ty, expectation, expr.span, expr.inner.span());
        Ok(())
    }

    /// Infer the type of a group expression.
    pub fn infer_group_expr(
        &mut self,
        expr: &mut HirGroupExpr<'hir>,
        expectation: &'hir HirTy<'hir>,
    ) -> HirResult<()> {
        self.infer(&mut expr.inner, expectation)?;
        self.constrain_eq(expectation, expr.ty, expr.span, expr.inner.span());
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
        self.constrain_eq(expr.ty, expectation, expr.span, expr.operand.span());
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
        let arguments = match &expr.op {
            HirBinaryOp::And
            | HirBinaryOp::Or
            | HirBinaryOp::Eq
            | HirBinaryOp::Neq
            | HirBinaryOp::Lt
            | HirBinaryOp::Gt
            | HirBinaryOp::Lte
            | HirBinaryOp::Gte => vec![expr.lhs.ty(), expr.rhs.ty()],
            HirBinaryOp::Add
            | HirBinaryOp::Sub
            | HirBinaryOp::Mul
            | HirBinaryOp::Div
            | HirBinaryOp::Rem => {
                vec![expr.lhs.ty(), expr.rhs.ty(), expectation]
            }
        };

        self.constrain_instance(
            trait_name,
            expr.span,
            method_name,
            expr.span,
            arguments,
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
            HirTy::Meta(v)
                if !self
                    .substitution(v)
                    .map(|t| t.is_equal_to_meta(v))
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
            | HirTy::Variable(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Meta(_)
            | HirTy::Nominal(_) => Ok(ty),
        }
    }

    /// Get the substitution for the given type variable.
    pub fn substitution(&self, v: &HirMetaTy) -> Option<&'hir HirTy<'hir>> {
        self.substitutions.get(v.index as usize).copied()
    }

    /// Determine if the substitution at the given index is equal to its own type variable.
    pub fn is_substitution_equal_to_self(&self, v: &HirMetaTy) -> bool {
        self.substitution(v)
            .map(|t| t.is_equal_to_meta(v))
            .unwrap_or(false)
    }

    /// Determine if the given variable type occurs in another type.
    ///
    /// This is required for HM type inference, as we need to determine if a type variable points to
    /// itself. An example is a constraint like `$0 = fn() -> $0`, which cannot be satisfied ever.
    pub fn occurs_in(&self, v: &HirMetaTy, ty: &'hir HirTy<'hir>) -> bool {
        match ty {
            // If the variable points to a substitution of itself, it occurs in itself
            HirTy::Meta(o) if !self.is_substitution_equal_to_self(o) => true,
            HirTy::Meta(o) => o.index == v.index,
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
            | HirTy::Variable(_)
            | HirTy::Pointer(_) => false,
        }
    }
}

impl<'hir> TypingContext<'hir> {
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
            HirTy::Meta(v) if !self.is_substitution_equal_to_self(v) => {
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
                    .module_query_db
                    .query_struct_by_name(n.name)
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
        self.module_query_db
            .query_trait_by_name(constraint.name)
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
            expectation,
            actual,
            expectation_loc,
            actual_loc,
        }: EqualityConstraint<'hir>,
    ) -> HirResult<()> {
        match (&expectation, &actual) {
            (HirTy::Meta(lhs), HirTy::Meta(rhs)) if lhs.index == rhs.index => Ok(()),
            (HirTy::Nominal(a), HirTy::Nominal(b)) if std::ptr::eq(a.name, b.name) => Ok(()),
            (HirTy::Meta(v), _) if !self.is_substitution_equal_to_self(v) => {
                let constraint = EqualityConstraint {
                    expectation: self
                        .substitution(v)
                        .unwrap_or_else(|| ice!("unreachable: tested variable no longer exists")),
                    actual,
                    expectation_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (_, HirTy::Meta(v)) if !self.is_substitution_equal_to_self(v) => {
                let constraint = EqualityConstraint {
                    expectation,
                    actual: self
                        .substitution(v)
                        .unwrap_or_else(|| ice!("unreachable: tested variable no longer exists")),
                    expectation_loc,
                    actual_loc,
                };
                self.unify_eq(constraint)
            }
            (HirTy::Meta(v), _) => {
                if self.occurs_in(v, actual) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: actual_loc,
                        right: expectation_loc,
                    }));
                }
                self.substitutions[v.index as usize] = actual;
                Ok(())
            }
            (_, HirTy::Meta(v)) => {
                if self.occurs_in(v, expectation) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: expectation_loc,
                        right: actual_loc,
                    }));
                }
                self.substitutions[v.index as usize] = expectation;
                Ok(())
            }
            (HirTy::Pointer(a), HirTy::Pointer(b)) => {
                let constraint = EqualityConstraint {
                    expectation: a.inner,
                    expectation_loc,
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
                        span: expectation_loc,
                    }));
                }
                let constraint = EqualityConstraint {
                    expectation: definition.return_type,
                    expectation_loc,
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
                        expectation_loc,
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
                expected_loc: expectation_loc,
                actual_type: rhs.format(),
                expected_type: lhs.format(),
            })),
        }
    }

    /// Create a fresh meta variable.
    pub fn fresh_meta_variable(&mut self) -> &'hir HirTy<'hir> {
        let index = self.substitutions.len() as u32;
        let ty = self.arena.types().get_meta_ty(index);
        self.substitutions.push(ty);
        ty
    }

    /// Eliminates all type variables from within the given type with the substitutions that are
    /// provided in `instantiations`.
    ///
    /// We cannot use the recursive `HirModuleTypeCheckerPass::visit_ty` here, because we need to
    /// completely isolate the instantiated variables from the rest of the type environment.
    fn eliminate_type_variables_within_ty(
        &mut self,
        instantiations: &mut HashMap<(u32, u32), &'hir HirTy<'hir>>,
        ty: &'hir HirTy<'hir>,
    ) -> &'hir HirTy<'hir> {
        match ty {
            HirTy::Variable(v) => instantiations
                .entry((v.depth, v.index))
                .or_insert_with(|| self.fresh_meta_variable()),
            HirTy::Pointer(p) => {
                let inner = self.eliminate_type_variables_within_ty(instantiations, p.inner);
                self.arena.types().get_pointer_ty(inner)
            }
            HirTy::Meta(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Integer32(_)
            | HirTy::Nominal(_) => ty,
            HirTy::Function(_) => {
                ice!("should not be possible to pass functions as arguments")
            }
            HirTy::Uninitialized(_) => {
                ice!("uninitialized type made it to the type checker")
            }
        }
    }
}
