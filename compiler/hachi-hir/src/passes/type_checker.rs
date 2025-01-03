// use crate::context::LocalContext;
// use crate::error::{HirError, HirResult, TypeFieldInfiniteRecursionError, UnknownTypeError};
// use crate::fun::{HirFun, HirFunction, HirIntrinsicFunction};
// use crate::rec::HirRecord;
// use crate::ty::{HirFunctionTy, HirNominalTy, HirPointerTy, HirReferenceTy, HirTy};
// use crate::HirModule;
// use hachi_syntax::Span;
// use std::collections::VecDeque;
//
// pub enum Constraint<'hir> {
//     Eq(&'hir HirTy, &'hir HirTy),
// }
//
// /// A type checker for HIR modules.
// ///
// /// The type checker is also responsible for type inference. Our type system is based on the Hindley
// /// Milner type system.
// pub struct TypeChecker<'hir> {
//     module: &'hir mut HirModule,
//     local_let_bindings: LocalContext<HirTy>,
//     constraints: Vec<Constraint<'hir>>,
//     substitutions: Vec<HirTy>,
//     /// The deque of functions that are currently being visited.
//     ///
//     /// This is a deque to support nested functions or lambdas in the future.
//     local_functions: VecDeque<&'hir HirFunction>,
// }
//
// impl<'hir> TypeChecker<'hir> {
//     /// Visit the module and type-check it.
//     ///
//     /// Once a module has been through this pass, all of its types are guaranteed to be
//     /// well-formed, and the entire module is guaranteed to be fully typed.
//     pub fn visit(&mut self) -> HirResult<()> {
//         self.local_let_bindings.enter_scope();
//         // Insert all the types into the local type environment.
//         {
//             for rec in records.values_mut() {
//                 self.visit_module_rec(rec)?;
//             }
//         }
//         {
//             // Insert all the functions into the local let-binding environment. Because this happens at
//             // the module level, it makes them globally available to all functions.
//             for fun in self.module.functions.values_mut() {
//                 self.visit_module_fun(fun)?;
//             }
//         }
//         self.local_let_bindings.leave_scope();
//         Ok(())
//     }
//
//     pub fn visit_module_rec(&self, rec: &mut HirRecord) -> HirResult<()> {
//         // Check if any of the fields are infinitely recursive.
//         for (field, field_ty) in rec.fields.iter() {
//             let field_ty = field_ty.as_ref();
//             // If there is no non-nullable indirection here, we must break
//             let is_infinitely_recursive = matches!(
//                 field_ty.ty.as_ref(), HirTy::Nominal(n) if n.name.name == rec.name.name
//             ) || matches!(
//                 field_ty.ty.as_ref(), HirTy::Reference(r) if matches!(
//                     r.get_deep_inner(), HirTy::Nominal(n) if n.name.name == rec.name.name
//                 )
//             );
//             if is_infinitely_recursive {
//                 return Err(HirError::TypeFieldInfiniteRecursion(
//                     TypeFieldInfiniteRecursionError {
//                         type_name: rec.name.name.to_owned(),
//                         offending_field: field.clone(),
//                         span: field_ty.span.clone(),
//                     },
//                 ));
//             }
//         }
//         Ok(())
//     }
//
//     pub fn visit_module_fun(&self, fun: &mut HirFun) -> HirResult<()> {
//         match fun {
//             HirFun::Function(f) => self.visit_function(f),
//             HirFun::Intrinsic(f) => self.visit_intrinsic_function(f),
//         }
//     }
//
//     pub fn visit_function(&self, fun: &mut HirFunction) -> HirResult<()> {
//         self.visit_type(&mut fun.return_type)
//     }
//
//     pub fn visit_intrinsic_function(&self, fun: &mut HirIntrinsicFunction) -> HirResult<()> {
//         todo!()
//     }
// }
//
// impl<'hir> TypeChecker<'hir> {
//     pub fn new() -> Self {
//         Self {
//             local_let_bindings: LocalContext::new(),
//             constraints: Vec::new(),
//             substitutions: Vec::new(),
//             local_functions: VecDeque::new(),
//         }
//     }
//
//     pub fn fresh_type_id(&self) -> usize {
//         self.substitutions.len()
//     }
//
//     /// Generate a fresh type variable.
//     pub fn fresh_type_variable(&self) -> HirTy {
//         HirTy::new_var(self.fresh_type_id(), Span::empty())
//     }
//
//     /// Find the type of the given let binding in the local type environment.
//     pub fn lookup_let_binding(&'hir self, name: &str, span: &Span) -> HirResult<&'hir HirTy> {
//         let ty = self
//             .local_let_bindings
//             .find(name)
//             .ok_or(HirError::UnknownType(UnknownTypeError {
//                 name: name.to_owned(),
//                 span: span.clone(),
//             }))?;
//         Ok(ty)
//     }
//
//     /// Replaces the given type with a fresh type variable if it is uninitialized.
//     pub fn coalesce_uninitialized(&self, ty: &mut HirTy) -> HirResult<()> {
//         if ty.is_uninitialized() {
//             *ty = self.fresh_type_variable();
//         }
//         Ok(())
//     }
// }
//
// impl<'hir> Default for TypeChecker<'hir> {
//     fn default() -> Self {
//         Self::new()
//     }
// }
//
// impl<'hir> TypeChecker<'hir> {
//     pub fn visit_type(&mut self, ty: &HirTy) -> HirResult<()> {
//         match ty {
//             HirTy::Nominal(t) => self.visit_nominal_ty(t),
//             HirTy::Function(t) => self.visit_function_ty(t),
//             HirTy::Pointer(t) => self.visit_pointer_ty(t),
//             HirTy::Reference(t) => self.visit_reference_ty(t),
//             HirTy::Uninitialized
//             | HirTy::Boolean(_)
//             | HirTy::Unit(_)
//             | HirTy::Integer32(_)
//             | HirTy::Variable(_) => Ok(()),
//         }
//     }
//
//     /// Visit a constant constructor type.
//     ///
//     /// This ensures that the type that is being referenced is defined in the current environment.
//     pub fn visit_nominal_ty(&mut self, ty: &HirNominalTy) -> HirResult<()> {
//         Ok(())
//     }
//
//     /// Visit a Function constructor type.
//     pub fn visit_function_ty(&mut self, ty: &HirFunctionTy) -> HirResult<()> {
//         for ty in &ty.parameters {
//             self.visit_type(ty)?;
//         }
//         self.visit_type(&ty.return_type)
//     }
//
//     /// Visit a pointer constructor type.
//     pub fn visit_pointer_ty(&mut self, ty: &HirPointerTy) -> HirResult<()> {
//         self.visit_type(&ty.inner)
//     }
//
//     /// Visit a reference constructor type.
//     pub fn visit_reference_ty(&mut self, ty: &HirReferenceTy) -> HirResult<()> {
//         self.visit_type(&ty.inner)
//     }
// }
//
// #[cfg(test)]
// mod tests {
//     // use crate::passes::type_checker::TypeChecker;
//     //
//     // macro_rules! assert_hir_module {
//     //     ($input:expr) => {{
//     //         let mut lexer = hachi_syntax::Lexer::new($input);
//     //         let mut parser = hachi_syntax::Parser::new(&mut lexer);
//     //         let translation_unit = assert_ok!(parser.parse());
//     //         let mut lowering_pass = hachi_syntax_lower::SyntaxLoweringPass::new();
//     //         let module = lowering_pass
//     //             .visit_translation_unit(&translation_unit)
//     //             .expect("failed to lower translation unit");
//     //         module
//     //     }};
//     // }
//     //
//     // #[test]
//     // fn test_synthesis_of_generic_functions() {
//     //     let mut module = assert_hir_module!(
//     //         r#"
//     //     fn id<T>(x: T) -> T {
//     //       return x;
//     //     }
//     //     "#
//     //     );
//     //     let mut tc = TypeChecker::new();
//     //     tc.visit(&mut module).expect("failed to type-check module");
//     // }
// }
