mod error;

use crate::error::SyntaxLoweringResult;
use hachi_hir::ty::HirTy;
use hachi_hir::HirModule;
use hachi_syntax::{FunctionItem, IntrinsicFunctionItem, IntrinsicTypeItem, Item, Stmt, TypeItem};

/// Translation pass that lowers the `hachi-syntax` AST into the HIR representation.
#[derive(Debug)]
pub struct SyntaxLoweringPass<'hir> {
    module: HirModule<'hir>,
}

impl<'hir> SyntaxLoweringPass<'hir> {
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
        }
    }

    pub fn visit_item(&mut self, node: &Item) -> SyntaxLoweringResult<()> {
        match node {
            Item::Function(f) => self.visit_function_item(f),
            Item::IntrinsicFunction(f) => self.visit_intrinsic_function_item(f),
            Item::Type(t) => self.visit_type_item(t),
            Item::IntrinsicType(t) => self.visit_intrinsic_type_item(t),
        }
    }

    pub fn visit_function_item(&mut self, node: &FunctionItem) -> SyntaxLoweringResult<()> {
        todo!()
    }

    pub fn visit_intrinsic_function_item(
        &mut self,
        node: &IntrinsicFunctionItem,
    ) -> SyntaxLoweringResult<()> {
        todo!()
    }

    pub fn visit_type_item(&mut self, node: &TypeItem) -> SyntaxLoweringResult<()> {
        todo!()
    }

    pub fn visit_intrinsic_type_item(
        &mut self,
        node: &IntrinsicTypeItem,
    ) -> SyntaxLoweringResult<()> {
        let ty = HirTy::new_const(node.name.name.to_owned(), node.name.span().clone());
        self.module.types.insert(node.name.name.as_str(), ty);
        Ok(())
    }

    pub fn visit_stmt(&mut self, node: &'hir Stmt) -> SyntaxLoweringResult<()> {
        todo!()
    }

    pub fn visit_expr(&mut self, node: &'hir Stmt) -> SyntaxLoweringResult<()> {
        todo!()
    }
}
