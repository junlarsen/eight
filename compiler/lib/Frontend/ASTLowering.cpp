//===----- ASTLowering.cpp ------------------------------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/ASTLowering.h"

using namespace xd;
using namespace llvm;

auto ASTLoweringPass::run() -> std::unique_ptr<TIRModule> {
  return std::make_unique<TIRModule>();
}
