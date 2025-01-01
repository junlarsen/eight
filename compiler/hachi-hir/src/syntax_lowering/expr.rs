use crate::error::HirResult;
use crate::expr::{
    HirAssignExpr, HirBinaryOp, HirBinaryOpExpr, HirBooleanLiteralExpr, HirCallExpr,
    HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirExpr, HirGroupExpr,
    HirIntegerLiteralExpr, HirOffsetIndexExpr, HirReferenceExpr, HirUnaryOp, HirUnaryOpExpr,
};
use crate::syntax_lowering::SyntaxLoweringPass;
use crate::ty::HirTy;
use hachi_syntax::{
    AssignExpr, BinaryOp, BinaryOpExpr, BooleanLiteralExpr, BracketIndexExpr, CallExpr,
    ConstructExpr, ConstructorExprArgument, DotIndexExpr, Expr, GroupExpr, IntegerLiteralExpr,
    ReferenceExpr, UnaryOp, UnaryOpExpr,
};

impl<'ast> SyntaxLoweringPass<'ast> {
    pub fn visit_expr(&mut self, node: &'ast Expr) -> HirResult<Box<HirExpr>> {
        match node {
            Expr::Assign(e) => self.visit_assign_expr(e),
            Expr::Call(e) => self.visit_call_expr(e),
            Expr::Construct(e) => self.visit_construct_expr(e),
            Expr::Group(e) => self.visit_group_expr(e),
            Expr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            Expr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            Expr::UnaryOp(e) => self.visit_unary_op_expr(e),
            Expr::BinaryOp(e) => self.visit_binary_op_expr(e),
            Expr::DotIndex(e) => self.visit_dot_index_expr(e),
            Expr::BracketIndex(e) => self.visit_bracket_index_expr(e),
            Expr::Reference(e) => self.visit_reference_expr(e),
        }
    }

    pub fn visit_assign_expr(&mut self, node: &'ast AssignExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Assign(HirAssignExpr {
            span: node.span().clone(),
            lhs: self.visit_expr(node.lhs.as_ref())?,
            rhs: self.visit_expr(node.rhs.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_call_expr(&mut self, node: &'ast CallExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Call(HirCallExpr {
            span: node.span().clone(),
            callee: self.visit_expr(node.callee.as_ref())?,
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_expr(a))
                .collect::<HirResult<Vec<_>>>()?,
            type_arguments: node
                .type_arguments
                .iter()
                .map(|t| self.visit_type(t))
                .collect::<HirResult<Vec<_>>>()?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_construct_expr(&mut self, node: &'ast ConstructExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Construct(HirConstructExpr {
            span: node.span().clone(),
            callee: self.visit_type(node.callee.as_ref())?,
            arguments: node
                .arguments
                .iter()
                .map(|a| self.visit_constructor_expr_argument(a))
                .collect::<HirResult<Vec<_>>>()?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_constructor_expr_argument(
        &mut self,
        node: &'ast ConstructorExprArgument,
    ) -> HirResult<Box<HirConstructExprArgument>> {
        let hir = HirConstructExprArgument {
            span: node.span().clone(),
            field: self.visit_identifier(node.field.as_ref())?,
            expr: self.visit_expr(node.expr.as_ref())?,
        };
        Ok(Box::new(hir))
    }

    pub fn visit_group_expr(&mut self, node: &'ast GroupExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Group(HirGroupExpr {
            span: node.span().clone(),
            inner: self.visit_expr(node.inner.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_integer_literal_expr(
        &mut self,
        node: &'ast IntegerLiteralExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::IntegerLiteral(HirIntegerLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_boolean_literal_expr(
        &mut self,
        node: &'ast BooleanLiteralExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::BooleanLiteral(HirBooleanLiteralExpr {
            span: node.span().clone(),
            value: node.value,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_unary_op_expr(&mut self, node: &'ast UnaryOpExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::UnaryOp(HirUnaryOpExpr {
            span: node.span().clone(),
            operand: self.visit_expr(node.operand.as_ref())?,
            op: self.visit_unary_op(&node.op)?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_binary_op_expr(&mut self, node: &'ast BinaryOpExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::BinaryOp(HirBinaryOpExpr {
            span: node.span().clone(),
            lhs: self.visit_expr(node.lhs.as_ref())?,
            rhs: self.visit_expr(node.rhs.as_ref())?,
            op: self.visit_binary_op(&node.op)?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_dot_index_expr(&mut self, node: &'ast DotIndexExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::ConstantIndex(HirConstantIndexExpr {
            span: node.span().clone(),
            origin: self.visit_expr(node.origin.as_ref())?,
            index: self.visit_identifier(node.index.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_bracket_index_expr(
        &mut self,
        node: &'ast BracketIndexExpr,
    ) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::OffsetIndex(HirOffsetIndexExpr {
            span: node.span().clone(),
            origin: self.visit_expr(node.origin.as_ref())?,
            index: self.visit_expr(node.index.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_reference_expr(&mut self, node: &'ast ReferenceExpr) -> HirResult<Box<HirExpr>> {
        let hir = HirExpr::Reference(HirReferenceExpr {
            span: node.span().clone(),
            name: self.visit_identifier(node.name.as_ref())?,
            ty: Box::new(HirTy::Uninitialized),
        });
        Ok(Box::new(hir))
    }

    pub fn visit_unary_op(&mut self, node: &'ast UnaryOp) -> HirResult<HirUnaryOp> {
        match node {
            UnaryOp::Not => Ok(HirUnaryOp::Not),
            UnaryOp::Neg => Ok(HirUnaryOp::Neg),
            UnaryOp::Deref => Ok(HirUnaryOp::Deref),
            UnaryOp::AddressOf => Ok(HirUnaryOp::AddressOf),
        }
    }

    pub fn visit_binary_op(&mut self, node: &'ast BinaryOp) -> HirResult<HirBinaryOp> {
        match node {
            BinaryOp::Add => Ok(HirBinaryOp::Add),
            BinaryOp::Sub => Ok(HirBinaryOp::Sub),
            BinaryOp::Mul => Ok(HirBinaryOp::Mul),
            BinaryOp::Div => Ok(HirBinaryOp::Div),
            BinaryOp::Rem => Ok(HirBinaryOp::Rem),
            BinaryOp::Eq => Ok(HirBinaryOp::Eq),
            BinaryOp::Neq => Ok(HirBinaryOp::Neq),
            BinaryOp::Lt => Ok(HirBinaryOp::Lt),
            BinaryOp::Gt => Ok(HirBinaryOp::Gt),
            BinaryOp::Le => Ok(HirBinaryOp::Le),
            BinaryOp::Ge => Ok(HirBinaryOp::Ge),
            BinaryOp::Lte => Ok(HirBinaryOp::Lte),
            BinaryOp::Gte => Ok(HirBinaryOp::Gte),
            BinaryOp::And => Ok(HirBinaryOp::And),
            BinaryOp::Or => Ok(HirBinaryOp::Or),
        }
    }
}
