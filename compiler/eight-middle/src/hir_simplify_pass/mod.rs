//! Simplification pass for HIR.

use crate::context::CompileContext;
use crate::hir::{
    HirAddressOfExpr, HirAssignExpr, HirBlockStmt, HirBooleanLiteralExpr, HirBreakStmt,
    HirCallExpr, HirConstantIndexExpr, HirConstructExpr, HirConstructExprArgument, HirContinueStmt,
    HirDerefExpr, HirExpr, HirExprStmt, HirFunction, HirGroupExpr, HirIfStmt, HirInstance,
    HirIntegerLiteralExpr, HirLetStmt, HirLoopStmt, HirModule, HirOffsetIndexExpr,
    HirReferenceExpr, HirReferenceSymbol, HirReturnStmt, HirStmt,
};

pub struct HirSimplifyPass<'be> {
    cc: &'be CompileContext<'be>,
}

impl<'be> HirSimplifyPass<'be> {
    pub fn new(cc: &'be CompileContext<'be>) -> Self {
        Self { cc }
    }
}

impl<'be> HirSimplifyPass<'be> {
    pub fn visit_module(&mut self, module: &mut HirModule<'be>) {
        for function in module.body.functions.values_mut() {
            self.visit_function(function);
        }
        for instance in module.body.instances.iter_mut() {
            self.visit_instance(instance);
        }
    }

    pub fn visit_function(&mut self, function: &mut HirFunction<'be>) {
        for stmt in function.body.iter_mut() {
            self.visit_stmt(stmt);
        }
    }

    pub fn visit_instance(&mut self, instance: &mut HirInstance<'be>) {
        for member in instance.members.iter_mut() {
            self.visit_function(member);
        }
    }

    pub fn visit_stmt(&mut self, stmt: &mut HirStmt<'be>) {
        match stmt {
            HirStmt::Let(s) => self.visit_let_stmt(s),
            HirStmt::Return(s) => self.visit_return_stmt(s),
            HirStmt::Loop(s) => self.visit_loop_stmt(s),
            HirStmt::Break(s) => self.visit_break_stmt(s),
            HirStmt::Continue(s) => self.visit_continue_stmt(s),
            HirStmt::If(s) => self.visit_if_stmt(s),
            HirStmt::Expr(s) => self.visit_expr_stmt(s),
            HirStmt::Block(s) => self.visit_block_stmt(s),
        }
    }

    pub fn visit_let_stmt(&mut self, stmt: &mut HirLetStmt<'be>) {
        self.visit_expr(&mut stmt.value);
    }

    pub fn visit_return_stmt(&mut self, stmt: &mut HirReturnStmt<'be>) {
        if let Some(inner) = &mut stmt.value {
            self.visit_expr(inner);
        }
    }

    pub fn visit_loop_stmt(&mut self, stmt: &mut HirLoopStmt<'be>) {
        for stmt in stmt.body.iter_mut() {
            self.visit_stmt(stmt);
        }
    }

    pub fn visit_break_stmt(&mut self, _: &mut HirBreakStmt) {}

    pub fn visit_continue_stmt(&mut self, _: &mut HirContinueStmt) {}

    pub fn visit_if_stmt(&mut self, stmt: &mut HirIfStmt<'be>) {
        self.visit_expr(&mut stmt.condition);
        for stmt in stmt.happy_path.iter_mut() {
            self.visit_stmt(stmt);
        }
        for stmt in stmt.unhappy_path.iter_mut() {
            self.visit_stmt(stmt);
        }
    }

    pub fn visit_expr_stmt(&mut self, stmt: &mut HirExprStmt<'be>) {
        self.visit_expr(&mut stmt.expr);
    }

    pub fn visit_block_stmt(&mut self, stmt: &mut HirBlockStmt<'be>) {
        for stmt in stmt.body.iter_mut() {
            self.visit_stmt(stmt);
        }
    }

    pub fn visit_expr(&mut self, expr: &mut HirExpr<'be>) {
        match expr {
            HirExpr::IntegerLiteral(e) => self.visit_integer_literal_expr(e),
            HirExpr::BooleanLiteral(e) => self.visit_boolean_literal_expr(e),
            HirExpr::Assign(e) => self.visit_assign_expr(e),
            HirExpr::Reference(e) => self.visit_reference_expr(e),
            HirExpr::ConstantIndex(e) => self.visit_constant_index_expr(e),
            HirExpr::OffsetIndex(e) => self.visit_offset_index_expr(e),
            HirExpr::Call(e) => self.visit_call_expr(e),
            HirExpr::Construct(e) => self.visit_construct_expr(e),
            HirExpr::Group(e) => self.visit_group_expr(e),
            HirExpr::AddressOf(e) => self.visit_address_of_expr(e),
            HirExpr::Deref(e) => self.visit_deref_expr(e),
        }
    }

    pub fn visit_integer_literal_expr(&mut self, _: &mut HirIntegerLiteralExpr<'be>) {}

    pub fn visit_boolean_literal_expr(&mut self, _: &mut HirBooleanLiteralExpr<'be>) {}

    pub fn visit_assign_expr(&mut self, expr: &mut HirAssignExpr<'be>) {
        self.visit_expr(&mut expr.lhs);
        self.visit_expr(&mut expr.rhs);
    }

    pub fn visit_reference_expr(&mut self, expr: &mut HirReferenceExpr<'be>) {
        self.visit_reference_symbol(&mut expr.kind)
    }

    fn visit_reference_symbol(&mut self, _: &mut HirReferenceSymbol<'be>) {}

    pub fn visit_constant_index_expr(&mut self, expr: &mut HirConstantIndexExpr<'be>) {
        self.visit_expr(&mut expr.origin);
    }

    pub fn visit_offset_index_expr(&mut self, expr: &mut HirOffsetIndexExpr<'be>) {
        self.visit_expr(&mut expr.origin);
        self.visit_expr(&mut expr.index);
    }

    pub fn visit_call_expr(&mut self, expr: &mut HirCallExpr<'be>) {
        self.visit_expr(&mut expr.callee);
        for argument in expr.arguments.iter_mut() {
            self.visit_expr(argument);
        }
    }

    pub fn visit_construct_expr(&mut self, expr: &mut HirConstructExpr<'be>) {
        for argument in expr.arguments.iter_mut() {
            self.visit_construct_expr_argument(argument);
        }
    }

    pub fn visit_construct_expr_argument(&mut self, expr: &mut HirConstructExprArgument<'be>) {
        self.visit_expr(&mut expr.expr);
    }

    pub fn visit_group_expr(&mut self, expr: &mut HirGroupExpr<'be>) {
        self.visit_expr(&mut expr.inner);
    }

    pub fn visit_address_of_expr(&mut self, expr: &mut HirAddressOfExpr<'be>) {
        self.visit_expr(&mut expr.inner);
    }

    pub fn visit_deref_expr(&mut self, expr: &mut HirDerefExpr<'be>) {
        self.visit_expr(&mut expr.inner);
    }
}
