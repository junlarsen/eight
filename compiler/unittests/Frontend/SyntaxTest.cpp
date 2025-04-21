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

  auto Members = Root->findChildren({SyntaxKind::Function, SyntaxKind::Struct});
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
