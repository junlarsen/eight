//===----- SyntaxTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Syntax.h"
#include "Support.h"
#include "xd/Frontend/AST.h"
#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/Parser.h"
#include "llvm/Support/MemoryBuffer.h"
#include <gtest/gtest.h>

using namespace llvm;
using namespace xd;

TEST(SyntaxTest, GraphSearching) {
  auto Root = SyntaxNode::getRoot(
      std::make_shared<GreenNode>(SyntaxKind::TranslationUnit, 20));
  auto FunctionChild = SyntaxNode::get(
      Root, std::make_shared<GreenNode>(SyntaxKind::Function, 10), 0, 0);
  auto StructChild = SyntaxNode::get(
      Root, std::make_shared<GreenNode>(SyntaxKind::Struct, 10), 10, 1);
  ASSERT_EQ(FunctionChild->getParent(), Root);
  ASSERT_EQ(StructChild->getParent(), Root);
  ASSERT_EQ(Root->getParent(), std::nullopt);

  auto FoundFn = Root->findChild(SyntaxKind::Function);
  ASSERT_EQ(FoundFn, FunctionChild);
  auto FoundStruct = Root->findChild(SyntaxKind::Struct);
  ASSERT_EQ(FoundStruct, StructChild);

  auto SiblingStruct = FunctionChild->findSibling(SyntaxKind::Struct);
  ASSERT_EQ(SiblingStruct, StructChild);

  auto Members = Root->findChildren(isDeclSyntaxKind);
  ASSERT_TRUE(Members.has_value());
  ASSERT_EQ(Members->size(), 2);
  ASSERT_EQ(Members->front()->getParent(), Root);
  // Because Function was registered before struct, it should be the first child
  ASSERT_EQ(Members->front(), FunctionChild);
  ASSERT_EQ(Members->back(), StructChild);
}

TEST(SyntaxTest, CastIntoSyntaxTree) {
  auto IdentifierNode = SyntaxNode::getRoot(
      std::make_shared<GreenToken>(SyntaxKind::Identifier, "bar"));
  auto F = Identifier::cast(IdentifierNode);
  ASSERT_TRUE(F.has_value());
  ASSERT_EQ((*F)->getName(), "bar");
  ASSERT_EQ((*F)->getLocation(), SourceLocation(0, 3));

  // PointerType should be able to llvm::dyn_cast its inner type. Here we
  // construct a *int.
  auto TypeRoot = SyntaxNode::getRoot(
      std::make_shared<GreenNode>(SyntaxKind::PointerType, 4));
  auto InnerNode = SyntaxNode::get(
      TypeRoot, std::make_shared<GreenNode>(SyntaxKind::NamedType, 3), 0, 0);
  auto Name = SyntaxNode::get(
      InnerNode, std::make_shared<GreenToken>(SyntaxKind::Identifier, "int"), 0,
      0);

  auto PtrType = ASTPointerType::cast(TypeRoot);
  ASSERT_TRUE(PtrType.has_value());
  ASSERT_TRUE(isa<ASTPointerType>(**PtrType));
  ASSERT_TRUE(isa<ASTType>(**PtrType));
  ASSERT_TRUE(isa<ASTNode>(**PtrType));
  auto InnerType = (*PtrType)->getInnerType();
  ASSERT_TRUE(InnerType.has_value());
  ASSERT_TRUE(isa<ASTNamedType>(**InnerType));
  ASSERT_TRUE(isa<ASTType>(**InnerType));
  ASSERT_TRUE(isa<ASTNode>(**InnerType));
  auto NamedType = cast<ASTNamedType>(**InnerType);
  auto Ident = NamedType.getName();
  ASSERT_TRUE(Ident.has_value());
  ASSERT_EQ((*Ident)->getName(), "int");
}

TEST(SyntaxTest, ParseBinaryExprIntoTree) {
  auto Ctx = test::getParser("1 + 5 * 2");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTBinaryExpr>(**Expr));
  auto BinExpr = cast<ASTBinaryExpr>(**Expr);
  ASSERT_EQ(BinExpr.getOperator(), ASTBinaryOperator::Add);
  auto RHS = BinExpr.getRHS();
  ASSERT_TRUE(RHS.has_value());
  ASSERT_TRUE(isa<ASTBinaryExpr>(**RHS));
  auto RHSExpr = cast<ASTBinaryExpr>(**RHS);
  ASSERT_EQ(RHSExpr.getOperator(), ASTBinaryOperator::Mul);
}

TEST(SyntaxTest, ParseUnaryExprIntoTree) {
  auto Ctx = test::getParser("-*x");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTUnaryExpr>(**Expr));
  auto UnaryExpr = cast<ASTUnaryExpr>(**Expr);
  ASSERT_EQ(UnaryExpr.getOperator(), ASTUnaryOperator::Minus);
  auto Operand = UnaryExpr.getOperand();
  ASSERT_TRUE(Operand.has_value());
  ASSERT_TRUE(isa<ASTUnaryExpr>(**Operand));
  auto OperandExpr = cast<ASTUnaryExpr>(**Operand);
  ASSERT_EQ(OperandExpr.getOperator(), ASTUnaryOperator::Deref);
}

TEST(SyntaxTest, ParseGroupExprIntoTree) {
  auto Ctx = test::getParser("((a))");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTGroupExpr>(**Expr));
  auto GroupExpr = cast<ASTGroupExpr>(**Expr);
  auto InnerExpr = GroupExpr.getInnerExpr();
  ASSERT_TRUE(InnerExpr.has_value());
  ASSERT_TRUE(isa<ASTGroupExpr>(**InnerExpr));
}

TEST(SyntaxTest, ParseReferenceExprIntoTree) {
  auto Ctx = test::getParser("aa");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTReferenceExpr>(**Expr));
  auto ReferenceExpr = cast<ASTReferenceExpr>(**Expr);
  auto Name = ReferenceExpr.getName();
  ASSERT_TRUE(Name.has_value());
  ASSERT_EQ((*Name)->getName(), "aa");
}

TEST(SyntaxTest, ParseConstantIndexExprIntoTree) {
  auto Ctx = test::getParser("a.b");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTConstantIndexExpr>(**Expr));
  auto ConstantIndexExpr = cast<ASTConstantIndexExpr>(**Expr);
  auto Origin = ConstantIndexExpr.getOrigin();
  ASSERT_TRUE(Origin.has_value());
  ASSERT_TRUE(isa<ASTReferenceExpr>(**Origin));
  auto Index = ConstantIndexExpr.getIndex();
  ASSERT_TRUE(Index.has_value());
  ASSERT_EQ((*Index)->getName(), "b");
}

TEST(SyntaxTest, ParseIntegerLiteralExprIntoTree) {
  auto Ctx = test::getParser("100");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(**Expr));
  auto IntegerLiteralExpr = cast<ASTIntegerLiteralExpr>(**Expr);
  ASSERT_EQ(IntegerLiteralExpr.getValue(), 100);
}

TEST(SyntaxTest, ParseBooleanLiteralExprIntoTree) {
  {
    auto Ctx = test::getParser("true");
    Ctx->P.parseExpr();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Expr = ASTExpr::cast(RedTree);
    ASSERT_TRUE(Expr.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Expr));
    ASSERT_TRUE(isa<ASTBooleanLiteralExpr>(**Expr));
    auto BooleanLiteralExpr = cast<ASTBooleanLiteralExpr>(**Expr);
    ASSERT_EQ(BooleanLiteralExpr.getValue(), true);
  }
  {
    auto Ctx = test::getParser("false");
    Ctx->P.parseExpr();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Expr = ASTExpr::cast(RedTree);
    ASSERT_TRUE(Expr.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Expr));
    ASSERT_TRUE(isa<ASTBooleanLiteralExpr>(**Expr));
    auto BooleanLiteralExpr = cast<ASTBooleanLiteralExpr>(**Expr);
    ASSERT_EQ(BooleanLiteralExpr.getValue(), false);
  }
}

TEST(SyntaxTest, ParseCallExprIntoTree) {
  {
    auto Ctx = test::getParser("f[int](1, 2, 3)");
    Ctx->P.parseExpr();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Expr = ASTExpr::cast(RedTree);
    ASSERT_TRUE(Expr.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Expr));
    ASSERT_TRUE(isa<ASTCallExpr>(**Expr));
    auto CallExpr = cast<ASTCallExpr>(**Expr);

    auto TypeArgList = CallExpr.getTypeArgumentList();
    ASSERT_TRUE(TypeArgList.has_value());
    auto TypeArgs = (*TypeArgList)->getTypeArguments();
    ASSERT_TRUE(TypeArgs.has_value());
    ASSERT_EQ(TypeArgs->size(), 1);
    ASSERT_TRUE(isa<ASTNamedType>(TypeArgs->at(0).get()));

    auto ArgList = CallExpr.getArgumentList();
    ASSERT_TRUE(ArgList.has_value());
    auto Args = (*ArgList)->getArguments();
    ASSERT_TRUE(Args.has_value());
    ASSERT_EQ(Args->size(), 3);
    ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(Args->at(0).get()));
    ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(Args->at(1).get()));
    ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(Args->at(2).get()));
  }
  {
    auto Ctx = test::getParser("f()");
    Ctx->P.parseExpr();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Expr = ASTExpr::cast(RedTree);
    ASSERT_TRUE(Expr.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Expr));
    ASSERT_TRUE(isa<ASTCallExpr>(**Expr));
    auto CallExpr = cast<ASTCallExpr>(**Expr);

    auto TypeArgList = CallExpr.getTypeArgumentList();
    ASSERT_FALSE(TypeArgList.has_value());

    auto ArgList = CallExpr.getArgumentList();
    ASSERT_TRUE(ArgList.has_value());
    auto Args = (*ArgList)->getArguments();
    ASSERT_TRUE(Args.has_value());
    ASSERT_EQ(Args->size(), 0);
  }
}

TEST(SyntaxTest, ParseConstructionExprIntoTree) {
  auto Ctx = test::getParser("new Vec2D { x = 1, y = 2 }");
  Ctx->P.parseExpr();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Expr = ASTExpr::cast(RedTree);
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Expr));
  ASSERT_TRUE(isa<ASTConstructionExpr>(**Expr));
  auto ConstructionExpr = cast<ASTConstructionExpr>(**Expr);

  auto Type = ConstructionExpr.getConstructorType();
  ASSERT_TRUE(Type.has_value());
  ASSERT_TRUE(isa<ASTNamedType>(**Type));

  auto Members = ConstructionExpr.getMemberList();
  ASSERT_TRUE(Members.has_value());
  auto MemberList = (*Members)->getMembers();
  ASSERT_TRUE(MemberList.has_value());
  ASSERT_EQ(MemberList->size(), 2);

  auto XMember = MemberList->at(0);
  ASSERT_TRUE(XMember->getName().has_value());
  ASSERT_EQ(XMember->getName()->get()->getName(), "x");
  ASSERT_TRUE(XMember->getValue().has_value());
  ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(XMember->getValue()->get()));
}

TEST(SyntaxTest, ParseLetStmtIntoTree) {
  auto Ctx = test::getParser("let f: i32 = 0;");
  Ctx->P.parseStmt();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Stmt = ASTStmt::cast(RedTree);
  ASSERT_TRUE(Stmt.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Stmt));
  ASSERT_TRUE(isa<ASTLetStmt>(**Stmt));
  auto LetStmt = cast<ASTLetStmt>(**Stmt);

  auto Name = LetStmt.getName();
  ASSERT_TRUE(Name.has_value());
  ASSERT_EQ(Name->get()->getName(), "f");

  auto TypeAnnotation = LetStmt.getTypeAnnotation();
  ASSERT_TRUE(TypeAnnotation.has_value());
  ASSERT_TRUE(isa<ASTNamedType>(**TypeAnnotation));

  auto InitializerExpr = LetStmt.getInitializerExpr();
  ASSERT_TRUE(InitializerExpr.has_value());
  ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(**InitializerExpr));
}

TEST(SyntaxTest, ParseIfStmtIntoTree) {
  {
    auto Ctx = test::getParser("if (true) { } else { let b = 1; }");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTIfStmt>(**Stmt));
    auto IfStmt = cast<ASTIfStmt>(**Stmt);

    auto ThenBody = IfStmt.getThenBody();
    ASSERT_TRUE(ThenBody.has_value());
    auto ThenStmts = (*ThenBody)->getStmtList();
    ASSERT_TRUE(ThenStmts.has_value());
    ASSERT_EQ(ThenStmts->size(), 0);

    auto ElseBody = IfStmt.getElseBody();
    ASSERT_TRUE(ElseBody.has_value());
    auto ElseStmts = (*ElseBody)->getStmtList();
    ASSERT_TRUE(ElseStmts.has_value());
    ASSERT_EQ(ElseStmts->size(), 1);
  }
  {
    auto Ctx = test::getParser("if (true) { }");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTIfStmt>(**Stmt));
    auto IfStmt = cast<ASTIfStmt>(**Stmt);

    auto ElseBody = IfStmt.getElseBody();
    ASSERT_FALSE(ElseBody.has_value());
  }
}

TEST(SyntaxTest, ParseForStmtIntoTree) {
  {
    auto Ctx =
        test::getParser("for (let i = 0; i < 10; i = i + 1) { let x = 0; }");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTForStmt>(**Stmt));
    auto ForStmt = cast<ASTForStmt>(**Stmt);

    auto ForInitializer = ForStmt.getInitializer();
    ASSERT_TRUE(ForInitializer.has_value());
    ASSERT_TRUE(ForInitializer->get()->getName().has_value());
    ASSERT_EQ(ForInitializer->get()->getName()->get()->getName(), "i");
    ASSERT_FALSE(ForInitializer->get()->getTypeAnnotation().has_value());
    ASSERT_TRUE(ForInitializer->get()->getInitializer().has_value());
    ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(
        ForInitializer->get()->getInitializer()->get()));

    auto ForCondition = ForStmt.getCondition();
    ASSERT_TRUE(ForCondition.has_value());
    ASSERT_TRUE(ForCondition->get()->getExpr().has_value());
    ASSERT_TRUE(isa<ASTBinaryExpr>(ForCondition->get()->getExpr()->get()));

    auto ForIncrement = ForStmt.getIncrement();
    ASSERT_TRUE(ForIncrement.has_value());
    ASSERT_TRUE(ForIncrement->get()->getExpr().has_value());
    // Assignments are binary operators.
    ASSERT_TRUE(isa<ASTBinaryExpr>(ForIncrement->get()->getExpr()->get()));

    auto ForBody = ForStmt.getBody();
    ASSERT_TRUE(ForBody.has_value());
    ASSERT_TRUE(ForBody->get()->getStmtList().has_value());
    ASSERT_EQ(ForBody->get()->getStmtList()->size(), 1);
  }
  {
    auto Ctx = test::getParser("for (;;) {}");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTForStmt>(**Stmt));
    auto ForStmt = cast<ASTForStmt>(**Stmt);

    ASSERT_FALSE(ForStmt.getInitializer().has_value());
    ASSERT_FALSE(ForStmt.getCondition().has_value());
    ASSERT_FALSE(ForStmt.getIncrement().has_value());
  }
}

TEST(SyntaxTest, ParseBreakStmtIntoTree) {
  auto Ctx = test::getParser("break;");
  Ctx->P.parseStmt();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Stmt = ASTStmt::cast(RedTree);
  ASSERT_TRUE(Stmt.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Stmt));
  ASSERT_TRUE(isa<ASTBreakStmt>(**Stmt));
}

TEST(SyntaxTest, ParseContinueStmtIntoTree) {
  auto Ctx = test::getParser("continue;");
  Ctx->P.parseStmt();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Stmt = ASTStmt::cast(RedTree);
  ASSERT_TRUE(Stmt.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Stmt));
  ASSERT_TRUE(isa<ASTContinueStmt>(**Stmt));
}

TEST(SyntaxTest, ParseReturnStmtIntoTree) {
  {
    auto Ctx = test::getParser("return;");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTReturnStmt>(**Stmt));
    auto ReturnStmt = cast<ASTReturnStmt>(**Stmt);
    ASSERT_FALSE(ReturnStmt.getReturnExpr().has_value());
  }
  {
    auto Ctx = test::getParser("return 1;");
    Ctx->P.parseStmt();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Stmt = ASTStmt::cast(RedTree);
    ASSERT_TRUE(Stmt.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Stmt));
    ASSERT_TRUE(isa<ASTReturnStmt>(**Stmt));
    auto ReturnStmt = cast<ASTReturnStmt>(**Stmt);

    auto ReturnExpr = ReturnStmt.getReturnExpr();
    ASSERT_TRUE(ReturnExpr.has_value());
    ASSERT_TRUE(isa<ASTIntegerLiteralExpr>(ReturnExpr->get()));
  }
}

TEST(SyntaxTest, ParseExprStmtIntoTree) {
  auto Ctx = test::getParser("1 + 1;");
  Ctx->P.parseStmt();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Stmt = ASTStmt::cast(RedTree);
  ASSERT_TRUE(Stmt.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Stmt));
  ASSERT_TRUE(isa<ASTExprStmt>(**Stmt));
  auto ExprStmt = cast<ASTExprStmt>(**Stmt);

  auto Expr = ExprStmt.getExpr();
  ASSERT_TRUE(Expr.has_value());
  ASSERT_TRUE(isa<ASTBinaryExpr>(Expr->get()));
}

TEST(SyntaxTest, ParseFunctionDeclIntoTree) {
  {
    auto Ctx = test::getParser("fn id[T](el: T) -> T { return el; }");
    Ctx->P.parseDecl();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Decl = ASTDecl::cast(RedTree);
    ASSERT_TRUE(Decl.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Decl));
    ASSERT_TRUE(isa<ASTFunctionDecl>(**Decl));
    auto FunctionDecl = cast<ASTFunctionDecl>(**Decl);
    ASSERT_FALSE(FunctionDecl.isIntrinsic());

    ASSERT_TRUE(FunctionDecl.getReturnType().has_value());
    ASSERT_TRUE(isa<ASTNamedType>(FunctionDecl.getReturnType()->get()));

    auto TypeParameterList = FunctionDecl.getTypeParameterList();
    ASSERT_TRUE(TypeParameterList.has_value());
    ASSERT_TRUE(TypeParameterList->get()->getTypeParameters().has_value());
    ASSERT_EQ(TypeParameterList->get()->getTypeParameters().value().size(), 1);
    auto TypeParameter =
        TypeParameterList->get()->getTypeParameters().value().at(0);
    ASSERT_TRUE(TypeParameter->getName().has_value());
    ASSERT_EQ((*TypeParameter->getName())->getName(), "T");

    auto ParameterList = FunctionDecl.getParameterList();
    ASSERT_TRUE(ParameterList.has_value());
    ASSERT_TRUE(ParameterList->get()->getParameters().has_value());
    ASSERT_EQ(ParameterList->get()->getParameters().value().size(), 1);
    auto Parameter = ParameterList->get()->getParameters().value().at(0);
    ASSERT_TRUE(Parameter->getName().has_value());
    ASSERT_EQ((*Parameter->getName())->getName(), "el");

    auto Body = FunctionDecl.getBody();
    ASSERT_TRUE(Body.has_value());
    ASSERT_TRUE(Body->get()->getStmtList().has_value());
    ASSERT_EQ(Body->get()->getStmtList().value().size(), 1);
  }
  {
    auto Ctx = test::getParser("intrinsic_fn eat();");
    Ctx->P.parseDecl();
    auto GreenTree = Ctx->P.build();
    auto RedTree =
        buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
    auto Decl = ASTDecl::cast(RedTree);
    ASSERT_TRUE(Decl.has_value());
    ASSERT_TRUE(isa<ASTNode>(**Decl));
    ASSERT_TRUE(isa<ASTFunctionDecl>(**Decl));
    auto FunctionDecl = cast<ASTFunctionDecl>(**Decl);
    ASSERT_TRUE(FunctionDecl.isIntrinsic());

    ASSERT_FALSE(FunctionDecl.getBody().has_value());
  }
}

TEST(SyntaxTest, ParseStructDeclIntoTree) {
  auto Ctx = test::getParser("struct Vec2D { x: i32, y: i32 }");
  Ctx->P.parseDecl();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Decl = ASTDecl::cast(RedTree);
  ASSERT_TRUE(Decl.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Decl));
  ASSERT_TRUE(isa<ASTStructDecl>(**Decl));
  auto StructDecl = cast<ASTStructDecl>(**Decl);

  ASSERT_TRUE(StructDecl.getName().has_value());
  ASSERT_EQ((*StructDecl.getName())->getName(), "Vec2D");

  auto StructMemberList = StructDecl.getMemberList();
  ASSERT_TRUE(StructMemberList.has_value());
  ASSERT_TRUE((*StructMemberList)->getMembers().has_value());
  ASSERT_TRUE((*StructMemberList)->getMembers()->size() == 2);

  auto StructMember = (*StructMemberList)->getMembers()->at(0);
  ASSERT_TRUE(StructMember->getName().has_value());
  ASSERT_EQ((*StructMember->getName())->getName(), "x");
  ASSERT_TRUE(StructMember->getTypeAnnotation().has_value());
  ASSERT_TRUE(isa<ASTNamedType>(StructMember->getTypeAnnotation()->get()));
}

TEST(SyntaxTest, ParseIntrinsicTypeDeclIntoTree) {
  auto Ctx = test::getParser("intrinsic_type i32;");
  Ctx->P.parseDecl();
  auto GreenTree = Ctx->P.build();
  auto RedTree =
      buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *Ctx->DM);
  auto Decl = ASTDecl::cast(RedTree);
  ASSERT_TRUE(Decl.has_value());
  ASSERT_TRUE(isa<ASTNode>(**Decl));
  ASSERT_TRUE(isa<ASTIntrinsicTypeDecl>(**Decl));
  auto TypeDecl = cast<ASTIntrinsicTypeDecl>(**Decl);

  ASSERT_TRUE(TypeDecl.getName().has_value());
  ASSERT_EQ((*TypeDecl.getName())->getName(), "i32");
}
