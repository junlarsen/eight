use crate::error::HirResult;
use crate::syntax_lowering::SyntaxLoweringPass;
use crate::ty::HirTy;
use crate::HirName;
use hachi_syntax::{Identifier, Type};

/// Visitor for the `Type` AST node variants.
impl SyntaxLoweringPass<'_> {
    /// Translate a syntax identifier into a HIR name.
    pub fn visit_identifier(&mut self, node: &Identifier) -> HirResult<HirName> {
        Ok(HirName {
            name: node.name.to_owned(),
            span: node.span().clone(),
        })
    }

    /// Translate a syntax type into a HIR type.
    ///
    /// This function preserves generic types, and will simply replace T in the following code with
    /// a Const type. It is the job of the type-checker pass to replace this TConst type with a
    /// type variable using its type environment.
    ///
    /// ```text
    /// fn foo<T>(x: T) -> T {}
    /// ```
    #[allow(clippy::only_used_in_recursion)]
    pub fn visit_type(&mut self, node: &Type) -> HirResult<Box<HirTy>> {
        let ty = match node {
            Type::Unit(_) => HirTy::new_const("void", node.span()),
            Type::Integer32(_) => HirTy::new_const("i32", node.span()),
            Type::Boolean(_) => HirTy::new_const("bool", node.span()),
            // If the type is referring to a generic type that we have substituted before, we
            // use replace it with the substitution
            Type::Named(t) => match self.generic_substitutions.find(&t.name.name) {
                Some(ty) => ty.clone(),
                None => HirTy::new_const(&t.name.name, node.span()),
            },
            Type::Pointer(t) => HirTy::new_ptr(self.visit_type(t.inner.as_ref())?, node.span()),
            Type::Reference(t) => HirTy::new_ref(self.visit_type(t.inner.as_ref())?, node.span()),
        };
        Ok(Box::new(ty))
    }
}