//===----- AST.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/AST.h"
#include "xd/Frontend/TranslationUnit.h"

using namespace xd;
using namespace llvm;

// TODO: Probably move this definition into somewhere else
auto ASTTranslationUnit::debug(raw_ostream &OS) const -> void {
  OS << "ASTTranslationUnit with " << Modules.size() << " modules";
}
