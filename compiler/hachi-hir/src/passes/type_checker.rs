use crate::context::LocalContext;
use crate::error::{
    FunctionTypeMismatchError, HirError, HirResult, InvalidReferenceError,
    SelfReferentialTypeError, TypeFieldInfiniteRecursionError, TypeMismatchError, UnknownTypeError,
};
use crate::expr::HirExpr;
use crate::fun::{HirFun, HirFunction, HirIntrinsicFunction};
use crate::rec::HirRecord;
use crate::stmt::{HirExprStmt, HirLetStmt, HirStmt};
use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirReferenceTy, HirTy};
use crate::{HirModule, HirName};
use hachi_diagnostics::ice;
use hachi_span::Span;
use std::collections::{BTreeMap, VecDeque};

#[derive(Debug)]
pub enum Constraint {
    Eq(HirTy, HirTy),
    FieldProjection(HirTy, HirName, HirTy),
}

#[derive(Debug)]
pub struct TypingContext {
    constraints: Vec<Constraint>,
    substitutions: Vec<HirTy>,
    locals: LocalContext<HirTy>,
    current_function: VecDeque<HirFunctionTy>,
    /// Types derived from the module that we are type checking.
    records: BTreeMap<String, HirRecord>,
    scalars: BTreeMap<String, HirTy>,
}

impl Default for TypingContext {
    fn default() -> Self {
        Self {
            constraints: Vec::new(),
            substitutions: Vec::new(),
            locals: LocalContext::new(),
            current_function: VecDeque::new(),
            scalars: BTreeMap::new(),
            records: BTreeMap::new(),
        }
    }
}

impl TypingContext {
    pub fn new() -> Self {
        Default::default()
    }

    /// Crawl all the items from the module and insert them into the typing context.s
    pub fn explore_module(&mut self, module: &HirModule) {
        for fun in module.functions.values() {
            self.locals
                .add(&fun.name().name, HirTy::Function(fun.get_type()));
        }
        for rec in module.records.values() {
            self.records.insert(rec.name.name.to_owned(), rec.clone());
        }
        for (name, scalar) in module.scalars.iter() {
            self.scalars.insert(name.to_owned(), scalar.clone());
        }
    }

    pub fn constrain_field_projection(&mut self, ty: HirTy, field: HirName, inner: HirTy) {
        self.constraints
            .push(Constraint::FieldProjection(ty, field, inner))
    }

    pub fn constrain_eq(&mut self, a: HirTy, b: HirTy) {
        self.constraints.push(Constraint::Eq(a, b))
    }

    pub fn solve_constraints(&mut self) -> HirResult<()> {
        let constraints = self.constraints.drain(..).collect::<Vec<_>>();
        for constraint in constraints {
            match constraint {
                Constraint::Eq(lhs, rhs) => self.unify_eq(lhs, rhs)?,
                Constraint::FieldProjection(ty, field, inner) => {
                    self.unify_field_projection(ty, field, inner)?
                }
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
        ty: HirTy,
        field: HirName,
        inner: HirTy,
    ) -> HirResult<()> {
        match ty {
            HirTy::Variable(v) if !self.is_substitution_equal_to_self(v.var) => {
                self.unify_field_projection(self.substitutions[v.var].clone(), field, inner)
            }
            HirTy::Nominal(n) => {
                let ty = self
                    .records
                    .get(&n.name.name)
                    .unwrap_or_else(|| ice!("record type not found"));
                let Some(field) = ty.fields.get(&field.name) else {
                    ice!("field not found in record type");
                };
                self.unify_eq(field.ty.as_ref().clone(), inner)?;
                Ok(())
            }
            _ => {
                ice!("field projection constraint on non-record type");
            }
        }
    }

    /// Perform unification of two types.
    ///
    /// Unification is the process of determining if two types can be unified into a single type.
    /// Because we currently do not support subtyping, this is always an equivalence check.
    pub fn unify_eq(&mut self, lhs: HirTy, rhs: HirTy) -> HirResult<()> {
        match (&lhs, &rhs) {
            (HirTy::Variable(lhs), HirTy::Variable(rhs)) if lhs.var == rhs.var => Ok(()),
            (HirTy::Nominal(a), HirTy::Nominal(b)) if a.name.name == b.name.name => Ok(()),
            (HirTy::Variable(v), _) if !self.is_substitution_equal_to_self(v.var) => {
                self.unify_eq(self.substitutions[v.var].clone(), rhs)
            }
            (_, HirTy::Variable(v)) if !self.is_substitution_equal_to_self(v.var) => {
                self.unify_eq(lhs, self.substitutions[v.var].clone())
            }
            (HirTy::Variable(v), _) => {
                if self.occurs_in(v.var, &rhs) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: lhs.span().clone(),
                        right: rhs.span().clone(),
                    }));
                }
                self.substitutions[v.var] = rhs.clone();
                Ok(())
            }
            (_, HirTy::Variable(v)) => {
                if self.occurs_in(v.var, &lhs) {
                    return Err(HirError::SelfReferentialType(SelfReferentialTypeError {
                        left: lhs.span().clone(),
                        right: rhs.span().clone(),
                    }));
                }
                self.substitutions[v.var] = lhs.clone();
                Ok(())
            }
            (HirTy::Pointer(a), HirTy::Pointer(b)) => {
                self.unify_eq(a.inner.as_ref().clone(), b.inner.as_ref().clone())
            }
            (HirTy::Reference(a), HirTy::Reference(b)) => {
                self.unify_eq(a.inner.as_ref().clone(), b.inner.as_ref().clone())
            }
            (HirTy::Integer32(_), HirTy::Integer32(_)) => Ok(()),
            (HirTy::Boolean(_), HirTy::Boolean(_)) => Ok(()),
            (HirTy::Unit(_), HirTy::Unit(_)) => Ok(()),
            (HirTy::Function(a), HirTy::Function(b)) => {
                if a.parameters.len() != b.parameters.len() {
                    return Err(HirError::FunctionTypeMismatch(FunctionTypeMismatchError {
                        span: Span::empty(),
                    }));
                }
                self.unify_eq(
                    a.return_type.as_ref().clone(),
                    b.return_type.as_ref().clone(),
                )?;
                for (a, b) in a.parameters.iter().zip(b.parameters.iter()) {
                    self.unify_eq(a.as_ref().clone(), b.as_ref().clone())?;
                }
                Ok(())
            }
            (HirTy::Uninitialized, _) | (_, HirTy::Uninitialized) => {
                ice!("tried to unify with uninitialized type")
            }
            _ => Err(HirError::TypeMismatch(TypeMismatchError {
                span: Span::empty(),
            })),
        }
    }

    /// Create a fresh type variable.
    pub fn fresh_type_variable(&mut self) -> HirTy {
        let ty = HirTy::new_var(self.substitutions.len(), Span::empty());
        self.substitutions.push(ty.clone());
        ty
    }

    /// Set up an expression for type inference.
    ///
    /// This function adds the necessary constraints to the expression's type based on its expected
    /// type. The expected type is typically a type variable.
    ///
    /// Note that this function doesn't perform any substitution, it simply declares the necessary
    /// constraints for the expression in preparation for substitution.
    pub fn infer(&mut self, expr: &mut HirExpr, expected_ty: HirTy) -> HirResult<()> {
        match expr {
            // Integer literals are always i32 at the moment
            HirExpr::IntegerLiteral(_) => {
                self.constrain_eq(expected_ty, self.get_integer32_type());
                Ok(())
            }
            // Booleans always have the bool type
            HirExpr::BooleanLiteral(_) => {
                self.constrain_eq(expected_ty, self.get_boolean_type());
                Ok(())
            }
            // We don't want assignments to be chained, so we infer them as unit
            HirExpr::Assign(_) => {
                self.constrain_eq(expected_ty, self.get_unit_type());
                Ok(())
            }
            // If is a named type, we find the type in the local context, or throw a type reference
            // error if it doesn't exist.
            HirExpr::Reference(e) => {
                let ty = self
                    .locals
                    .find(&e.name.name)
                    .ok_or(HirError::InvalidReference(InvalidReferenceError {
                        name: e.name.name.to_owned(),
                        span: e.span.clone(),
                    }))?;
                self.constrain_eq(expected_ty, ty.clone());
                Ok(())
            }
            HirExpr::OffsetIndex(e) => {
                // The index must be an integer type
                self.constrain_eq(e.index.ty().clone(), self.get_integer32_type());
                // The origin must be a pointer of the element type
                let elem_ptr_ty = HirTy::new_ptr(Box::new(expected_ty.clone()), &e.span);
                self.constrain_eq(e.origin.ty().clone(), elem_ptr_ty);
                // The resulting type must be the element type
                self.constrain_eq(expected_ty, e.ty.as_ref().clone());
                Ok(())
            }
            HirExpr::ConstantIndex(e) => {
                self.constrain_field_projection(
                    e.origin.ty().clone(),
                    e.index.clone(),
                    expected_ty.clone(),
                );
                self.constrain_eq(expected_ty, e.ty.as_ref().clone());
                Ok(())
            }
            HirExpr::Call(e) => {
                let expected_args = e
                    .arguments
                    .iter()
                    .map(|a| Box::new(a.ty().clone()))
                    .collect::<Vec<_>>();
                let expected_signature =
                    HirTy::new_fun(Box::new(expected_ty.clone()), expected_args, &e.span);
                self.unify_eq(e.callee.ty().clone(), expected_signature)?;
                self.unify_eq(e.ty.as_ref().clone(), expected_ty)?;
                Ok(())
            }
            HirExpr::Construct(e) => {
                let HirTy::Nominal(n) = e.callee.as_ref() else {
                    ice!("construct expression callee is not a nominal type");
                };
                let ty = self
                    .records
                    .get(&n.name.name)
                    .unwrap_or_else(|| ice!("record type not found"))
                    .clone();
                // TODO: Check that the number of arguments matches the number of fields
                let pairs = ty.fields.iter().zip(e.arguments.iter()).collect::<Vec<_>>();
                for ((_, expected_ty), arg) in pairs {
                    self.unify_eq(arg.expr.ty().clone(), expected_ty.ty.as_ref().clone())?;
                }
                self.unify_eq(e.ty.as_ref().clone(), e.callee.as_ref().clone())?;
                self.unify_eq(e.ty.as_ref().clone(), expected_ty)?;
                Ok(())
            }
            HirExpr::AddressOf(e) => {
                // &a means that e is *inner, and expected_ty is *inner
                let result_ty = HirTy::new_ptr(Box::new(e.inner.ty().clone()), &e.span);
                self.constrain_eq(expected_ty, result_ty.clone());
                self.constrain_eq(e.ty.as_ref().clone(), result_ty);
                Ok(())
            }
            HirExpr::Deref(e) => {
                // *a means inner is a pointer type, and expected and e are unbox inner
                let inner_ptr = HirTy::new_ptr(Box::new(expected_ty.clone()), &e.span);
                self.constrain_eq(e.inner.ty().clone(), inner_ptr.clone());
                self.constrain_eq(e.ty.as_ref().clone(), expected_ty);
                Ok(())
            }
            // Grouping expressions take the type of the inner expression
            HirExpr::Group(e) => {
                self.infer(&mut e.inner, expected_ty.clone())?;
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
    pub fn substitute_expr(&mut self, expr: &mut HirExpr) -> HirResult<()> {
        match expr {
            HirExpr::IntegerLiteral(e) => self.substitute(&mut e.ty),
            HirExpr::BooleanLiteral(e) => self.substitute(&mut e.ty),
            HirExpr::Reference(e) => self.substitute(&mut e.ty),
            HirExpr::Assign(e) => {
                self.substitute_expr(&mut e.lhs)?;
                self.substitute_expr(&mut e.rhs)?;
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::OffsetIndex(e) => {
                self.substitute_expr(&mut e.origin)?;
                self.substitute_expr(&mut e.index)?;
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::ConstantIndex(e) => {
                self.substitute_expr(&mut e.origin)?;
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::Call(e) => {
                self.substitute_expr(&mut e.callee)?;
                for arg in e.arguments.iter_mut() {
                    self.substitute_expr(arg)?;
                }
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::Construct(e) => {
                for arg in e.arguments.iter_mut() {
                    self.substitute_expr(arg.expr.as_mut())?;
                }
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::AddressOf(e) => {
                self.substitute_expr(&mut e.inner)?;
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::Deref(e) => {
                self.substitute_expr(&mut e.inner)?;
                self.substitute(&mut e.ty)?;
                Ok(())
            }
            HirExpr::Group(e) => {
                self.substitute_expr(&mut e.inner)?;
                self.substitute(&mut e.ty)?;
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
    pub fn substitute(&mut self, ty: &mut HirTy) -> HirResult<()> {
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
                let mut sub = self.substitutions[v.var].clone();
                self.substitute(&mut sub)?;
                *ty = sub;
                Ok(())
            }
            // We substitute function types by substituting the return type and parameters
            HirTy::Function(f) => {
                for p in f.parameters.iter_mut() {
                    self.substitute(p)?;
                }
                self.substitute(&mut f.return_type)?;
                Ok(())
            }
            // We substitute pointer types by substituting the inner type
            HirTy::Pointer(p) => {
                self.substitute(&mut p.inner)?;
                Ok(())
            }
            // We substitute reference types by substituting the inner type
            HirTy::Reference(r) => {
                self.substitute(&mut r.inner)?;
                Ok(())
            }
            // Anything else is not a type variable or a constructor type, so there is nothing to
            // be done here.
            HirTy::Nominal(_) => ice!("nominal type should not be substituted"),
            HirTy::Integer32(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Variable(_)
            | HirTy::Uninitialized => Ok(()),
        }
    }

    /// Get the substitution for the given type variable.
    pub fn substitution(&self, var: usize) -> Option<&HirTy> {
        self.substitutions.get(var)
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
    pub fn occurs_in(&self, var: usize, ty: &HirTy) -> bool {
        match ty {
            // If the variable points to a substitution of itself, it occurs in itself
            HirTy::Variable(v) if !self.is_substitution_equal_to_self(v.var) => true,
            HirTy::Variable(v) => v.var == var,
            HirTy::Function(t) => {
                self.occurs_in(var, &t.return_type)
                    || t.parameters.iter().any(|p| self.occurs_in(var, p))
            }
            // Non-constructor types cannot possibly occur in other types.
            HirTy::Nominal(_) => ice!("nominal type should not be substituted"),
            HirTy::Integer32(_)
            | HirTy::Boolean(_)
            | HirTy::Unit(_)
            | HirTy::Uninitialized
            | HirTy::Pointer(_)
            | HirTy::Reference(_) => false,
        }
    }
}

impl TypingContext {
    pub fn get_integer32_type(&self) -> HirTy {
        self.scalars
            .get("i32")
            .unwrap_or_else(|| ice!("builtin integer32 type not found"))
            .clone()
    }

    pub fn get_boolean_type(&self) -> HirTy {
        self.scalars
            .get("bool")
            .unwrap_or_else(|| ice!("builtin boolean type not found"))
            .clone()
    }

    pub fn get_unit_type(&self) -> HirTy {
        self.scalars
            .get("unit")
            .unwrap_or_else(|| ice!("builtin unit type not found"))
            .clone()
    }
}

pub struct TypeChecker();

impl TypeChecker {
    /// Type-check and perform type inference on the given module.
    pub fn visit(module: &mut HirModule) -> HirResult<()> {
        let mut cx = TypingContext::new();
        cx.locals.enter_scope();
        cx.explore_module(module);
        Self::visit_hir_module(&mut cx, module)?;
        cx.locals.leave_scope();
        Ok(())
    }

    /// Traverse the Hir module.
    pub fn visit_hir_module(cx: &mut TypingContext, node: &mut HirModule) -> HirResult<()> {
        for fun in node.functions.values_mut() {
            Self::visit_hir_function(cx, fun)?;
        }
        for rec in node.records.values_mut() {
            Self::visit_hir_record(cx, rec)?;
        }
        Ok(())
    }

    /// Traverse the function.
    pub fn visit_hir_function(cx: &mut TypingContext, node: &mut HirFun) -> HirResult<()> {
        match node {
            HirFun::Function(f) => Self::visit_function(cx, f),
            HirFun::Intrinsic(f) => Self::visit_intrinsic_function(cx, f),
        }
    }

    /// Traverse the intrinsic function.
    ///
    /// Intrinsic functions only require that their types are defined. Because type parameters
    /// passed to intrinsic functions are erased, we don't need to worry about them. The compiler
    /// assumes that the intrinsic functions are correct.
    ///
    /// TODO: If we wish to support extern "C" signatures, we should type check them here.
    pub fn visit_intrinsic_function(
        cx: &mut TypingContext,
        node: &mut HirIntrinsicFunction,
    ) -> HirResult<()> {
        Self::visit_type(cx, &mut node.return_type)?;
        for p in node.parameters.iter_mut() {
            Self::visit_type(cx, &mut p.ty)?;
        }
        Ok(())
    }

    /// Traverse the function.
    ///
    /// This ensures the types of the function's parameters and return type are correct, then it
    /// recurses down into the function body.
    pub fn visit_function(cx: &mut TypingContext, node: &mut HirFunction) -> HirResult<()> {
        // Create substitutions for all the type parameters.
        for ty in node.type_parameters.iter() {
            let substitution = HirTy::new_var(ty.name, ty.span.clone());
            cx.substitutions.push(substitution);
        }
        Self::visit_type(cx, &mut node.return_type)?;
        // Push the function's type onto the current stack, so that return statements can be checked
        // against the expected return type.
        cx.current_function.push_back(node.get_type());
        cx.locals.enter_scope();
        // Push all the function parameters into the local context.
        for p in node.parameters.iter_mut() {
            Self::visit_type(cx, &mut p.ty)?;
            cx.locals.add(&p.name.name, p.ty.as_ref().clone());
        }
        // Recurse down into the body.
        for stmt in node.body.iter_mut() {
            Self::visit_stmt(cx, stmt)?;
        }

        cx.locals.leave_scope();
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
    /// references itself by name, or by reference of any depth, it is infinitely recursive.
    pub fn visit_hir_record(cx: &mut TypingContext, node: &mut HirRecord) -> HirResult<()> {
        for field in node.fields.values_mut() {
            Self::visit_type(cx, &mut field.ty)?;
            // Check if the field directly references itself
            let is_directly_self_referential =
                matches!(field.ty.as_ref(), HirTy::Nominal(n) if n.name.name == node.name.name);
            // Check if the field directly references itself through a reference of any depth
            let is_indirectly_self_referential = matches!(field.ty.as_ref(), HirTy::Reference(r) if matches!(r.get_deep_inner(), HirTy::Nominal(n) if n.name.name == node.name.name));
            if is_directly_self_referential || is_indirectly_self_referential {
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
    pub fn visit_type(cx: &mut TypingContext, node: &mut HirTy) -> HirResult<()> {
        match node {
            HirTy::Nominal(t) => Self::visit_nominal_ty(cx, t),
            HirTy::Function(t) => Self::visit_function_ty(cx, t),
            HirTy::Pointer(t) => Self::visit_pointer_ty(cx, t),
            HirTy::Reference(t) => Self::visit_reference_ty(cx, t),
            HirTy::Variable(_) | HirTy::Integer32(_) | HirTy::Boolean(_) | HirTy::Unit(_) => Ok(()),
            // If the type was uninitialized by the lowering pass, we need to replace it with a
            // fresh type variable here.
            HirTy::Uninitialized => {
                *node = cx.fresh_type_variable();
                Ok(())
            }
        }
    }

    /// A named type is either a user-defined record type or a builtin type.
    ///
    /// If the given type is neither, we issue a type error.
    pub fn visit_nominal_ty(cx: &mut TypingContext, node: &mut HirNominalTy) -> HirResult<()> {
        if cx.locals.find(&node.name.name).is_some() {
            return Ok(());
        }
        if cx.records.contains_key(&node.name.name) {
            return Ok(());
        }
        Err(HirError::UnknownType(UnknownTypeError {
            name: node.name.name.to_owned(),
            span: node.name.span.clone(),
        }))
    }

    /// Visit a function type.
    pub fn visit_function_ty(cx: &mut TypingContext, node: &mut HirFunctionTy) -> HirResult<()> {
        for ty in node.parameters.iter_mut() {
            Self::visit_type(cx, ty)?;
        }
        Self::visit_type(cx, &mut node.return_type)
    }

    /// Visit a pointer type.
    pub fn visit_pointer_ty(cx: &mut TypingContext, node: &mut HirPointerTy) -> HirResult<()> {
        Self::visit_type(cx, &mut node.inner)
    }

    /// Visit a reference type.
    pub fn visit_reference_ty(cx: &mut TypingContext, node: &mut HirReferenceTy) -> HirResult<()> {
        Self::visit_type(cx, &mut node.inner)
    }

    /// Visit an expression and infer its type.
    pub fn visit_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
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
    pub fn visit_integer_literal_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::IntegerLiteral(e) = node else {
            ice!("visit_integer_literal_expr called with non-integer literal");
        };
        Self::visit_type(cx, &mut e.ty)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    /// Visit a boolean literal expression.
    ///
    /// The boolean literal expression's is always the boolean type.
    pub fn visit_boolean_literal_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::BooleanLiteral(e) = node else {
            ice!("visit_boolean_literal_expr called with non-boolean literal");
        };
        Self::visit_type(cx, &mut e.ty)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    /// Visit a group expression.
    ///
    /// The grouping expression's type is inferred from the inner expression.
    pub fn visit_group_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Group(e) = node else {
            ice!("visit_group_expr called with non-group expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    /// Visit a reference expression.
    ///
    /// For a reference expression, we get the local type from the local context, and infer the
    /// type according to that type.
    pub fn visit_reference_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Reference(e) = node else {
            ice!("visit_reference_expr called with non-reference expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        let Some(_) = cx.locals.find(&e.name.name) else {
            return Err(HirError::InvalidReference(InvalidReferenceError {
                name: e.name.name.to_owned(),
                span: e.span.clone(),
            }));
        };
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    /// Visit an assign expression.
    ///
    /// In order to prevent chaining of assignment such as `a = b = c`, we simply infer the type of
    /// the entire expression to be void.
    pub fn visit_assign_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Assign(e) = node else {
            ice!("visit_assign_expr called with non-assign expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.lhs)?;
        Self::visit_expr(cx, &mut e.rhs)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_offset_index_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::OffsetIndex(e) = node else {
            ice!("visit_offset_index_expr called with non-offset index expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.origin)?;
        Self::visit_expr(cx, &mut e.index)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_constant_index_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::ConstantIndex(e) = node else {
            ice!("visit_constant_index_expr called with non-constant index expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.origin)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_call_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Call(e) = node else {
            ice!("visit_call_expr called with non-call expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.callee)?;
        for arg in e.arguments.iter_mut() {
            Self::visit_expr(cx, arg)?;
        }
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_construct_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Construct(e) = node else {
            ice!("visit_construct_expr called with non-construct expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        for arg in e.arguments.iter_mut() {
            Self::visit_expr(cx, arg.expr.as_mut())?;
            let ty = arg.expr.ty().clone();
            cx.infer(arg.expr.as_mut(), ty)?;
        }
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_address_of_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::AddressOf(e) = node else {
            ice!("visit_address_of_expr called with non-address of expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    pub fn visit_deref_expr(cx: &mut TypingContext, node: &mut HirExpr) -> HirResult<()> {
        let HirExpr::Deref(e) = node else {
            ice!("visit_deref_expr called with non-deref expression");
        };
        Self::visit_type(cx, &mut e.ty)?;
        Self::visit_expr(cx, &mut e.inner)?;
        cx.infer(node, node.ty().clone())?;
        Ok(())
    }

    /// Visit a statement.
    pub fn visit_stmt(cx: &mut TypingContext, node: &mut HirStmt) -> HirResult<()> {
        match node {
            HirStmt::Let(s) => Self::visit_let_stmt(cx, s),
            HirStmt::Expr(e) => Self::visit_expr_stmt(cx, e),
            HirStmt::Loop(_) => todo!(),
            HirStmt::Return(_) => todo!(),
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
    pub fn visit_let_stmt(cx: &mut TypingContext, node: &mut HirLetStmt) -> HirResult<()> {
        // This coalesces let statements without a type annotation into a type variable.
        Self::visit_type(cx, &mut node.r#type)?;
        Self::visit_expr(cx, &mut node.value)?;
        cx.infer(&mut node.value, node.r#type.as_ref().clone())?;
        cx.solve_constraints()?;
        cx.substitute(&mut node.r#type)?;
        cx.substitute_expr(&mut node.value)?;
        cx.locals.add(&node.name.name, node.r#type.as_ref().clone());
        Ok(())
    }

    pub fn visit_expr_stmt(cx: &mut TypingContext, node: &mut HirExprStmt) -> HirResult<()> {
        Self::visit_expr(cx, &mut node.expr)?;
        cx.solve_constraints()?;
        cx.substitute_expr(&mut node.expr)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {}
