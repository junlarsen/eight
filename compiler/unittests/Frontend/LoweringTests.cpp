//===----- LoweringTests.cpp ----------------------------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/ASTLowering.h"
#include <gtest/gtest.h>

using namespace xd;
using namespace llvm;

TEST(LoweringTest, ScopeStack) {
  ScopeStack<int, int> Stack;
  Stack.enter();
  Stack.insert(1, 10);
  ASSERT_EQ(Stack.search(1), 10);
  ASSERT_EQ(Stack.search(2), std::nullopt);
  Stack.enter();
  Stack.insert(2, 20);
  Stack.insert(1, 30);
  ASSERT_EQ(Stack.search(2), 20);
  ASSERT_EQ(Stack.search(1), 30);
  Stack.exit();
  ASSERT_EQ(Stack.search(1), 10);
  ASSERT_EQ(Stack.search(2), std::nullopt);
  Stack.exit();
}
