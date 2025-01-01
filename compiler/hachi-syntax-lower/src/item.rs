use crate::error::SyntaxLoweringResult;
use crate::SyntaxLoweringPass;
use hachi_hir::fun::{
    HirFun, HirFunction, HirFunctionParameter, HirFunctionTypeParameter, HirIntrinsicFunction,
};
use hachi_hir::ty::HirTy;
use hachi_hir::HirModule;
use hachi_syntax::{
    FunctionItem, FunctionParameterItem, FunctionTypeParameterItem, IntrinsicFunctionItem,
    IntrinsicTypeItem, Item, Span, TranslationUnit, TypeItem,
};
use std::collections::BTreeMap;

impl SyntaxLoweringPass {
    pub fn visit_translation_unit(
        &mut self,
        node: &TranslationUnit,
    ) -> SyntaxLoweringResult<HirModule> {
        let mut module = HirModule::new();
        for item in &node.items {
            self.visit_item(&mut module, item)?;
        }
        Ok(module)
    }

    pub fn visit_item(&mut self, module: &mut HirModule, node: &Item) -> SyntaxLoweringResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(module, f),
            Item::IntrinsicFunction(f) => self.visit_intrinsic_function_item(module, f),
            Item::Type(t) => self.visit_type_item(module, t),
            Item::IntrinsicType(t) => self.visit_intrinsic_type_item(module, t),
        }
    }

    pub fn visit_function_item(
        &mut self,
        module: &mut HirModule,
        node: &FunctionItem,
    ) -> SyntaxLoweringResult<()> {
        let return_type = match &node.return_type {
            Some(t) => self.visit_type(t)?,
            None => Box::new(HirTy::new_const("void", &Span::empty())),
        };
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<SyntaxLoweringResult<Vec<_>>>()?;
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_function_type_parameter(p))
            .collect::<SyntaxLoweringResult<Vec<_>>>()?;
        let body = node
            .body
            .iter()
            .map(|stmt| self.visit_stmt(stmt))
            .collect::<SyntaxLoweringResult<Vec<_>>>()?;

        let fun = HirFun::Function(HirFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
            body,
        });
        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        module: &mut HirModule,
        node: &IntrinsicFunctionItem,
    ) -> SyntaxLoweringResult<()> {
        let return_type = self.visit_type(node.return_type.as_ref())?;
        let parameters = node
            .parameters
            .iter()
            .map(|p| self.visit_function_parameter(p))
            .collect::<SyntaxLoweringResult<Vec<_>>>()?;
        let type_parameters = node
            .type_parameters
            .iter()
            .map(|p| self.visit_function_type_parameter(p))
            .collect::<SyntaxLoweringResult<Vec<_>>>()?;

        let fun = HirFun::Intrinsic(HirIntrinsicFunction {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            type_parameters,
            parameters,
            return_type,
        });
        module.functions.insert(node.name.name.to_owned(), fun);
        Ok(())
    }

    pub fn visit_function_parameter(
        &mut self,
        node: &FunctionParameterItem,
    ) -> SyntaxLoweringResult<Box<HirFunctionParameter>> {
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
        node: &FunctionTypeParameterItem,
    ) -> SyntaxLoweringResult<Box<HirFunctionTypeParameter>> {
        let name = self.visit_identifier(node.name.as_ref())?;
        let hir = HirFunctionTypeParameter {
            span: node.span().clone(),
            name,
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
        node: &TypeItem,
    ) -> SyntaxLoweringResult<()> {
        let fields = node
            .members
            .iter()
            .map(|member| {
                let ty = self.visit_type(member.r#type.as_ref())?;
                Ok((member.name.name.to_owned(), ty))
            })
            .collect::<SyntaxLoweringResult<BTreeMap<_, _>>>()?;
        let ty = HirTy::new_record(fields, node.name.span());
        module.types.insert(node.name.name.to_owned(), ty);
        Ok(())
    }

    /// Declare an intrinsic type item.
    ///
    /// Intrinsic types are at the moment only scalar, so declaring them as constant types is fine.
    pub fn visit_intrinsic_type_item(
        &mut self,
        module: &mut HirModule,
        node: &IntrinsicTypeItem,
    ) -> SyntaxLoweringResult<()> {
        let ty = HirTy::new_const(&node.name.name, node.name.span());
        module.types.insert(node.name.name.to_owned(), ty);
        Ok(())
    }
}
