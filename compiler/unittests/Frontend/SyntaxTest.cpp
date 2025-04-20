//===----- SyntaxTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Syntax.h"
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
