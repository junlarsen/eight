use crate::context::LocalContext;
use crate::error::{HirError, HirResult, TypeFieldInfiniteRecursionError, UnknownTypeError};
use crate::fun::{HirFun, HirFunction, HirIntrinsicFunction};
use crate::ty::{HirConstantTy, HirFunctionTy, HirPointerTy, HirRecordTy, HirReferenceTy, HirTy};
use crate::HirModule;
use hachi_syntax::Span;
use std::collections::VecDeque;

pub enum Constraint<'hir> {
    Eq(&'hir HirTy, &'hir HirTy),
}

/// A type checker for HIR modules.
///
/// The type checker is also responsible for type inference. Our type system is based on the Hindley
/// Milner type system.
pub struct TypeChecker<'hir> {
    local_types: LocalContext<HirTy>,
    local_let_bindings: LocalContext<HirTy>,
    constraints: Vec<Constraint<'hir>>,
    substitutions: Vec<HirTy>,
    /// The deque of functions that are currently being visited.
    ///
    /// This is a deque to support nested functions or lambdas in the future.
    local_functions: VecDeque<&'hir HirFunction>,
}

impl<'hir> TypeChecker<'hir> {
    /// Visit the module and type-check it.
    ///
    /// Once a module has been through this pass, all of its types are guaranteed to be
    /// well-formed, and the entire module is guaranteed to be fully typed.
    pub fn visit(&mut self, module: &'hir mut HirModule) -> HirResult<()> {
        self.local_types.enter_scope();
        self.local_let_bindings.enter_scope();
        // Insert all the types into the local type environment.
        for (name, ty) in module.types.iter_mut() {
            self.visit_module_ty(name, ty)?;
        }
        // Insert all the functions into the local let-binding environment. Because this happens at
        // the module level, it makes them globally available to all functions.
        for (name, fun) in module.functions.iter_mut() {
            self.visit_module_fun(name, fun)?;
        }
        self.local_let_bindings.leave_scope();
        self.local_types.leave_scope();
        Ok(())
    }

    pub fn visit_module_ty(&mut self, name: &str, ty: &'hir mut HirTy) -> HirResult<()> {
        self.local_types.add(name, ty.clone());
        // Check if any of the fields are infinitely recursive.
        if let HirTy::Record(rec) = ty {
            for (field, field_ty) in &rec.fields {
                let field_ty = field_ty.as_ref();
                // A type is directly recursive if it has zero levels of indirection that are
                // unable to break the recursion. Because references are guaranteed to not be
                // null, they are considered to be directly recursive.
                let is_directly_equal = field_ty.is_exact_constant(name)
                    || matches!(&field_ty, HirTy::Reference(e) if e.get_deep_inner().is_exact_constant(name));
                if is_directly_equal {
                    return Err(HirError::TypeFieldInfiniteRecursion(
                        TypeFieldInfiniteRecursionError {
                            type_name: name.to_owned(),
                            offending_field: field.clone(),
                            span: field_ty.span().clone(),
                        },
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn visit_module_fun(&mut self, name: &str, fun: &'hir mut HirFun) -> HirResult<()> {
        // If the function has generic parameters, we need to replace all the TConst types from
        // the AST lowering pass with fresh type variables.
        self.local_types.enter_scope();
        // Create fresh type variables for all type parameters.
        for (i, ty) in fun.type_parameters().iter().enumerate() {
            self.local_types
                .add(&ty.syntax_name.name, HirTy::new_var(i, ty.span.clone()));
        }

        // With the type parameters in scope, we can visit the parameters, and if the current
        // parameters points to one of the type parameters, we replace it with the fresh type
        // that we just created.
        for p in fun.parameters_mut() {
            if let HirTy::Constant(v) = p.ty.as_ref() {
                if let Some(v) = self.local_types.find_local(&v.name) {
                    *p.ty = v.clone();
                }
            }
            self.visit_type(&p.ty)?;
        }

        // We now do the same for the return type.
        if let HirTy::Constant(v) = fun.return_type_mut() {
            if let Some(generic) = self.local_types.find_local(&v.name) {
                *fun.return_type_mut() = generic.clone();
            }
        }
        self.visit_type(fun.return_type())?;
        // Recurse into the function's body.
        match fun {
            HirFun::Function(f) => self.visit_function(f)?,
            HirFun::Intrinsic(f) => self.visit_intrinsic_function(f)?,
        }
        self.local_types.leave_scope();
        Ok(())
    }

    pub fn visit_function(&mut self, fun: &HirFunction) -> HirResult<()> {
        todo!()
    }

    pub fn visit_intrinsic_function(&mut self, fun: &HirIntrinsicFunction) -> HirResult<()> {
        todo!()
    }
}

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

    pub fn fresh_type_id(&self) -> usize {
        self.substitutions.len()
    }

    /// Generate a fresh type variable.
    pub fn fresh_type_variable(&self) -> HirTy {
        HirTy::new_var(self.fresh_type_id(), Span::empty())
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

    /// Replaces the given type with a fresh type variable if it is uninitialized.
    pub fn coalesce_uninitialized(&self, ty: &mut HirTy) -> HirResult<()> {
        if ty.is_uninitialized() {
            *ty = self.fresh_type_variable();
        }
        Ok(())
    }
}

impl<'hir> Default for TypeChecker<'hir> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'hir> TypeChecker<'hir> {
    pub fn visit_type(&mut self, ty: &HirTy) -> HirResult<()> {
        match ty {
            HirTy::Constant(t) => self.visit_constant_ty(t),
            HirTy::Function(t) => self.visit_function_ty(t),
            HirTy::Pointer(t) => self.visit_pointer_ty(t),
            HirTy::Reference(t) => self.visit_reference_ty(t),
            HirTy::Record(t) => self.visit_record_ty(t),
            HirTy::Uninitialized | HirTy::Variable(_) => Ok(()),
        }
    }

    /// Visit a zero-argument constructor type.
    ///
    /// This ensures that the type that is being referenced is defined in the current environment.
    pub fn visit_constant_ty(&mut self, ty: &HirConstantTy) -> HirResult<()> {
        self.lookup_type(&ty.name, &ty.span)?;
        Ok(())
    }

    /// Visit a Function constructor type.
    pub fn visit_function_ty(&mut self, ty: &HirFunctionTy) -> HirResult<()> {
        for ty in &ty.parameters {
            self.visit_type(ty)?;
        }
        self.visit_type(&ty.return_type)
    }

    /// Visit a pointer constructor type.
    pub fn visit_pointer_ty(&mut self, ty: &HirPointerTy) -> HirResult<()> {
        self.visit_type(&ty.inner)
    }

    /// Visit a reference constructor type.
    pub fn visit_reference_ty(&mut self, ty: &HirReferenceTy) -> HirResult<()> {
        self.visit_type(&ty.inner)
    }

    /// Visit a record constructor type.
    pub fn visit_record_ty(&mut self, ty: &HirRecordTy) -> HirResult<()> {
        for ty in ty.fields.values() {
            self.visit_type(ty.as_ref())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // use crate::passes::type_checker::TypeChecker;
    //
    // macro_rules! assert_hir_module {
    //     ($input:expr) => {{
    //         let mut lexer = hachi_syntax::Lexer::new($input);
    //         let mut parser = hachi_syntax::Parser::new(&mut lexer);
    //         let translation_unit = assert_ok!(parser.parse());
    //         let mut lowering_pass = hachi_syntax_lower::SyntaxLoweringPass::new();
    //         let module = lowering_pass
    //             .visit_translation_unit(&translation_unit)
    //             .expect("failed to lower translation unit");
    //         module
    //     }};
    // }
    //
    // #[test]
    // fn test_synthesis_of_generic_functions() {
    //     let mut module = assert_hir_module!(
    //         r#"
    //     fn id<T>(x: T) -> T {
    //       return x;
    //     }
    //     "#
    //     );
    //     let mut tc = TypeChecker::new();
    //     tc.visit(&mut module).expect("failed to type-check module");
    // }
}
