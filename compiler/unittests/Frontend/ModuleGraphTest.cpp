//===----- ModuleGraphTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/ModuleGraph.h"
#include <gtest/gtest.h>

using namespace xd;
using namespace llvm;

TEST(ModuleGraphTest, DetectCycles) {
  auto MG = ModuleGraph();
  // Register a main file that imports two others
  auto MainFD = SourceFileID(1);
  auto MainDep1 = SourceFileID(2);
  auto MainDep2 = SourceFileID(3);

  auto Edges1 = SmallVector<SourceFileID, 8>({MainDep1, MainDep2});
  auto Res1 = MG.addFileDependencies(MainFD, Edges1);
  ASSERT_FALSE(Res1.has_value());

  // However, when linking Dep1 back to Main, there should be errors.
  auto Edges2 = SmallVector<SourceFileID, 8>({MainFD});
  auto Res2 = MG.addFileDependencies(MainDep1, Edges2);
  ASSERT_TRUE(Res2.has_value());
  ASSERT_EQ(*Res2, MainFD);
}
