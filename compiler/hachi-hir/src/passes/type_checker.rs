use crate::context::LocalContext;
use crate::error::{
    FunctionTypeMismatchError, HirError, HirResult, TypeFieldInfiniteRecursionError,
    TypeMismatchError, UnknownTypeError,
};
use crate::expr::HirExpr;
use crate::fun::{HirFun, HirFunction, HirIntrinsicFunction};
use crate::rec::HirRecord;
use crate::stmt::{HirLetStmt, HirStmt};
use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirReferenceTy, HirTy};
use crate::HirModule;
use hachi_syntax::Span;
use std::collections::VecDeque;

pub enum Constraint {
    Eq(HirTy, HirTy),
}

/// A type checker for HIR modules.
///
/// The type checker is also responsible for type inference. Our type system is based on the Hindley
/// Milner type system.
pub struct TypeChecker<'hir> {
    local_types: LocalContext<HirTy>,
    local_let_bindings: LocalContext<HirTy>,
    constraints: Vec<Constraint>,
    substitutions: Vec<HirTy>,
    /// The deque of functions that are currently being visited.
    ///
    /// This is a deque to support nested functions or lambdas in the future.
    local_functions: VecDeque<&'hir HirFunction>,
}

/// Implementation block for inference and type checking functions.
impl<'hir> TypeChecker<'hir> {
    pub fn new() -> Self {
        Self {
            local_types: LocalContext::new(),
            local_let_bindings: LocalContext::new(),
            constraints: Vec::new(),
            substitutions: Vec::new(),
            local_functions: VecDeque::new(),
        }
    }

    /// Generate a fresh type variable.
    pub fn fresh_type_variable(&mut self) -> HirTy {
        let ty = HirTy::new_var(self.substitutions.len(), Span::empty());
        self.substitutions.push(ty.clone());
        ty
    }

    pub fn constrain_eq(&mut self, a: HirTy, b: HirTy) {
        self.constraints.push(Constraint::Eq(a, b))
    }

    /// Infer the type expression's type.
    ///
    /// This mutates the original expression type.
    pub fn infer(&mut self, expr: &mut HirExpr, expected_ty: &'hir HirTy) -> HirResult<()> {
        match expr {
            HirExpr::IntegerLiteral(_) => {
                self.constrain_eq(expected_ty.clone(), HirTy::new_i32(&Span::empty()));
                Ok(())
            }
            HirExpr::BooleanLiteral(_) => {
                self.constrain_eq(expected_ty.clone(), HirTy::new_bool(&Span::empty()));
                Ok(())
            }
            HirExpr::Reference(r) => {
                let ty = self.lookup_type(&r.name.name, &r.span)?;
                self.constrain_eq(expected_ty.clone(), ty.clone());
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Solve the constraints
    pub fn solve(&mut self) -> HirResult<()> {
        for constraint in self.constraints.drain(..) {
            match constraint {
                Constraint::Eq(lhs, rhs) => Self::unify(&lhs, &rhs)?,
            }
        }
        Ok(())
    }

    /// Unify two types.
    pub fn unify(lhs: &HirTy, rhs: &HirTy) -> HirResult<()> {
        match (lhs, rhs) {
            (HirTy::Variable(lhs), HirTy::Variable(rhs)) if lhs.name == rhs.name => Ok(()),
            (HirTy::Nominal(a), HirTy::Nominal(b)) if a.name.name == b.name.name => Ok(()),
            (HirTy::Pointer(a), HirTy::Pointer(b)) => Self::unify(&a.inner, &b.inner),
            (HirTy::Reference(a), HirTy::Reference(b)) => Self::unify(&a.inner, &b.inner),
            (HirTy::Integer32(_), HirTy::Integer32(_)) => Ok(()),
            (HirTy::Boolean(_), HirTy::Boolean(_)) => Ok(()),
            (HirTy::Unit(_), HirTy::Unit(_)) => Ok(()),
            (HirTy::Function(a), HirTy::Function(b)) => {
                if a.parameters.len() != b.parameters.len() {
                    return Err(HirError::FunctionTypeMismatch(FunctionTypeMismatchError {
                        span: Span::empty(),
                    }));
                }
                Self::unify(&a.return_type, &b.return_type)?;
                for (a, b) in a.parameters.iter().zip(b.parameters.iter()) {
                    Self::unify(a, b)?;
                }
                Ok(())
            }
            (HirTy::Uninitialized, _) | (_, HirTy::Uninitialized) => {
                panic!("ice: type is uninitialized")
            }
            _ => Err(HirError::TypeMismatch(TypeMismatchError {
                span: Span::empty(),
            })),
        }
    }

    pub fn occurs(&self, ty: &HirTy, matcher: &HirTy) -> bool {
        todo!()
    }

    /// Find the given type in the local type environment.
    pub fn lookup_type(&'hir self, name: &str, span: &Span) -> HirResult<&'hir HirTy> {
        let ty = self
            .local_types
            .find(name)
            .ok_or(HirError::UnknownType(UnknownTypeError {
                name: name.to_owned(),
                span: span.clone(),
            }))?;
        Ok(ty)
    }

    /// Find the type of the given let binding in the local type environment.
    pub fn lookup_let_binding(&'hir self, name: &str, span: &Span) -> HirResult<&'hir HirTy> {
        let ty = self
            .local_let_bindings
            .find(name)
            .ok_or(HirError::UnknownType(UnknownTypeError {
                name: name.to_owned(),
                span: span.clone(),
            }))?;
        Ok(ty)
    }
}

impl<'hir> Default for TypeChecker<'hir> {
    fn default() -> Self {
        Self::new()
    }
}

/// Implementation block for visiting modules and their items.
impl<'hir> TypeChecker<'hir> {
    /// Visit the module and type-check it.
    ///
    /// Once a module has been through this pass, all of its types are guaranteed to be
    /// well-formed, and the entire module is guaranteed to be fully typed.
    pub fn visit(&mut self, module: &mut HirModule) -> HirResult<()> {
        self.local_let_bindings.enter_scope();
        // Insert all the types into the local type environment.
        for rec in module.records.values_mut() {
            self.visit_module_rec(rec)?;
        }
        // Insert all the functions into the local let-binding environment. Because this happens at
        // the module level, it makes them globally available to all functions.
        for fun in module.functions.values_mut() {
            self.visit_module_fun(fun)?;
        }
        self.local_let_bindings.leave_scope();
        Ok(())
    }

    pub fn visit_module_rec(&self, rec: &mut HirRecord) -> HirResult<()> {
        // Check if any of the fields are infinitely recursive.
        for (field, field_ty) in rec.fields.iter() {
            let field_ty = field_ty.as_ref();
            // If there is no non-nullable indirection here, we must break
            let is_infinitely_recursive = matches!(
                field_ty.ty.as_ref(), HirTy::Nominal(n) if n.name.name == rec.name.name
            ) || matches!(
                field_ty.ty.as_ref(), HirTy::Reference(r) if matches!(
                    r.get_deep_inner(), HirTy::Nominal(n) if n.name.name == rec.name.name
                )
            );
            if is_infinitely_recursive {
                return Err(HirError::TypeFieldInfiniteRecursion(
                    TypeFieldInfiniteRecursionError {
                        type_name: rec.name.name.to_owned(),
                        offending_field: field.clone(),
                        span: field_ty.span.clone(),
                    },
                ));
            }
        }
        Ok(())
    }

    /// Visit a function definition in the module.
    pub fn visit_module_fun(&mut self, fun: &mut HirFun) -> HirResult<()> {
        match fun {
            HirFun::Function(f) => self.visit_function(f),
            HirFun::Intrinsic(f) => self.visit_intrinsic_function(f),
        }
    }

    /// Visit a function definition.
    ///
    /// This ensures that all the type parameters of the function exist in the local type
    /// environment.
    ///
    /// All parameters are pushed onto a local let-binding environment, and the entire body is
    /// recursed into.
    ///
    /// TODO: Consider how resetting the substitutions should be handled once we have nesting
    pub fn visit_function(&mut self, fun: &mut HirFunction) -> HirResult<()> {
        self.local_types.enter_scope();
        // Create substitutions for all the type parameters.
        for ty in fun.type_parameters.iter() {
            let substitution = HirTy::new_var(ty.name, ty.span.clone());
            self.substitutions.push(substitution);
        }
        // The visit of the return type is done first, as it doesn't have anything to do with the
        // scoping below.
        self.visit_type(&mut fun.return_type)?;

        // Push all parameters onto a new local environment before traversing the body.
        self.local_let_bindings.enter_scope();
        for p in fun.parameters.iter_mut() {
            self.visit_type(&mut p.ty)?;
            self.local_let_bindings
                .add(&p.name.name, p.ty.as_ref().clone());
        }
        for stmt in fun.body.iter_mut() {
            self.visit_stmt(stmt)?;
        }
        self.local_let_bindings.leave_scope();
        // Clear the substitution variables.
        self.substitutions.clear();
        self.local_types.leave_scope();
        Ok(())
    }

    /// Visit an intrinsic function definition.
    ///
    /// This ensures that all the type parameters of the function exist in the local type
    /// environment.
    pub fn visit_intrinsic_function(&mut self, fun: &mut HirIntrinsicFunction) -> HirResult<()> {
        self.local_types.enter_scope();
        for p in fun.parameters.iter_mut() {
            self.visit_type(&mut p.ty)?;
        }
        self.visit_type(&mut fun.return_type)?;
        self.local_types.leave_scope();
        Ok(())
    }
}

/// Implementation block for visiting statements.
impl<'hir> TypeChecker<'hir> {
    /// Visit a statement.
    pub fn visit_stmt(&mut self, stmt: &mut HirStmt) -> HirResult<()> {
        match stmt {
            HirStmt::Let(s) => self.visit_let_stmt(s),
            _ => Ok(()),
        }
    }

    pub fn visit_let_stmt(&mut self, stmt: &mut HirLetStmt) -> HirResult<()> {
        self.visit_type(&mut stmt.r#type)?;
        Ok(())
    }
}

/// Implementation block for visiting expressions.
impl<'hir> TypeChecker<'hir> {}

/// Implementation block for visiting types.
impl<'hir> TypeChecker<'hir> {
    /// Visit a type.
    ///
    /// Visiting a type should **ALWAYS** be done before traversing down into anything that could
    /// use the type. This is to ensure that there are no uninitialized types on a node being
    /// visited.
    pub fn visit_type(&mut self, ty: &mut HirTy) -> HirResult<()> {
        match ty {
            HirTy::Nominal(t) => self.visit_nominal_ty(t),
            HirTy::Function(t) => self.visit_function_ty(t),
            HirTy::Pointer(t) => self.visit_pointer_ty(t),
            HirTy::Reference(t) => self.visit_reference_ty(t),
            HirTy::Variable(_) | HirTy::Integer32(_) | HirTy::Boolean(_) | HirTy::Unit(_) => Ok(()),
            // If the type was uninitialized by the lowering pass, we need to replace it with a
            // fresh type variable here.
            HirTy::Uninitialized => {
                *ty = self.fresh_type_variable();
                Ok(())
            }
        }
    }

    /// Visit a zero-argument constructor type.
    ///
    /// This ensures that the type that is being referenced is defined in the current environment.
    pub fn visit_nominal_ty(&mut self, ty: &mut HirNominalTy) -> HirResult<()> {
        self.lookup_type(&ty.name.name, &ty.span)?;
        Ok(())
    }

    /// Visit a Function constructor type.
    pub fn visit_function_ty(&mut self, ty: &mut HirFunctionTy) -> HirResult<()> {
        for ty in ty.parameters.iter_mut() {
            self.visit_type(ty)?;
        }
        self.visit_type(&mut ty.return_type)
    }

    /// Visit a pointer constructor type.
    pub fn visit_pointer_ty(&mut self, ty: &mut HirPointerTy) -> HirResult<()> {
        self.visit_type(&mut ty.inner)
    }

    /// Visit a reference constructor type.
    pub fn visit_reference_ty(&mut self, ty: &mut HirReferenceTy) -> HirResult<()> {
        self.visit_type(&mut ty.inner)
    }
}

#[cfg(test)]
mod tests {}
