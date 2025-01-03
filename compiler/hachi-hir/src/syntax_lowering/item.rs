use crate::error::HirResult;
use crate::fun::{
    HirFun, HirFunction, HirFunctionParameter, HirFunctionTypeParameter, HirIntrinsicFunction,
};
use crate::rec::{HirRecord, HirRecordField};
use crate::syntax_lowering::SyntaxLoweringPass;
use crate::ty::HirTy;
use crate::HirModule;
use hachi_syntax::{
    FunctionItem, FunctionParameterItem, FunctionTypeParameterItem, IntrinsicFunctionItem, Item,
    Span, TranslationUnit, TypeItem,
};
use std::collections::BTreeMap;

impl<'ast> SyntaxLoweringPass<'ast> {
    pub fn visit_translation_unit<'hir>(
        &mut self,
        node: &'ast TranslationUnit,
    ) -> HirResult<HirModule<'hir>> {
        let mut module = HirModule::new();
        for item in &node.items {
            self.visit_item(&mut module, item)?;
        }
        Ok(module)
    }

    pub fn visit_item(&mut self, module: &mut HirModule, node: &'ast Item) -> HirResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(module, f),
            Item::IntrinsicFunction(f) => self.visit_intrinsic_function_item(module, f),
            Item::Type(t) => self.visit_type_item(module, t),
        }
    }

    pub fn visit_function_item(
        &mut self,
        module: &mut HirModule,
        node: &'ast FunctionItem,
    ) -> HirResult<()> {
        self.function_depth.push_back(node);
        // When we enter a function, we substitute all the type parameters with fresh type variables
        // so that the type checker knows these are generic types, and not constants. It is
        // currently safe to assume index for the type parameters, as we don't have higher order
        // functions or lambdas.
        self.generic_substitutions.enter_scope();
        let mut type_parameters = Vec::new();
        for (variable, type_parameter) in node.type_parameters.iter().enumerate() {
            self.generic_substitutions.add(
                &type_parameter.name.name,
                HirTy::new_var(variable, type_parameter.span().clone()),
            );
            // We also build the HIR representation, preserving the original name that was written
            // in code.
            let hir = self.visit_function_type_parameter(type_parameter, variable)?;
            type_parameters.push(hir);
        }
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => Box::new(HirTy::new_unit(&Span::empty())),
        };
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;
        let body = node
            .body
            .iter()
            .map(|stmt| self.visit_stmt(stmt))
            .collect::<HirResult<Vec<_>>>()?;

        let fun = HirFun::Function(HirFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
            body,
        });
        self.generic_substitutions.leave_scope();
        self.function_depth.pop_back();
        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        module: &mut HirModule,
        node: &'ast IntrinsicFunctionItem,
    ) -> HirResult<()> {
        self.generic_substitutions.enter_scope();
        let mut type_parameters = Vec::new();
        for (variable, type_parameter) in node.type_parameters.iter().enumerate() {
            self.generic_substitutions.add(
                &type_parameter.name.name,
                HirTy::new_var(variable, type_parameter.span().clone()),
            );
            // We also build the HIR representation, preserving the original name that was written
            // in code.
            let hir = self.visit_function_type_parameter(type_parameter, variable)?;
            type_parameters.push(hir);
        }

        let return_type = self.visit_type(node.return_type.as_ref())?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<HirResult<Vec<_>>>()?;

        let fun = HirFun::Intrinsic(HirIntrinsicFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
        });
        self.generic_substitutions.leave_scope();

        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &'ast FunctionParameterItem,
    ) -> HirResult<Box<HirFunctionParameter>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let ty = self.visit_type(node.r#type.as_ref())?;
        let hir = HirFunctionParameter {
            span: node.span().clone(),
            name,
            ty,
        };
        Ok(Box::new(hir))
    }

    pub fn visit_function_type_parameter(
        &mut self,
        node: &'ast FunctionTypeParameterItem,
        substitution_name: usize,
    ) -> HirResult<Box<HirFunctionTypeParameter>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let hir = HirFunctionTypeParameter {
            span: node.span().clone(),
            name: substitution_name,
            syntax_name: name,
        };
        Ok(Box::new(hir))
    }

    /// Declare a type item.
    ///
    /// We insert the type's structure into the module, and then derive the HIR type for each of the
    /// type members.
    ///
    /// This function does not check validity of the type members, as this is only a forward
    /// declaration. We have to do it like this in order to be able to support recursive types.
    ///
    /// While we do not support infinitely recursive types, we still need to support the following:
    ///
    /// ```text
    /// type Node = { value: i32, left: *Node, right: *Node, }
    /// ```
    pub fn visit_type_item(
        &mut self,
        module: &mut HirModule,
        node: &'ast TypeItem,
    ) -> HirResult<()> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let fields = node
            .members
            .iter()
            .map(|member| {
                let ty = self.visit_type(member.r#type.as_ref())?;
                let field = HirRecordField {
                    name: self.visit_identifier(member.name.as_ref())?,
                    ty,
                    span: member.span().clone(),
                };
                Ok((member.name.name.to_owned(), Box::new(field)))
            })
            .collect::<HirResult<BTreeMap<_, _>>>()?;
        let rec = HirRecord {
            name,
            fields,
            span: node.span().clone(),
        };
        module.records.insert(node.name.name.to_owned(), rec);
        Ok(())
    }
}
