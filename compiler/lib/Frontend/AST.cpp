//===----- AST.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/AST.h"

using namespace xd;
using namespace llvm;

auto ASTModuleDecl::getReferencedDependencyPaths() const
    -> std::vector<std::string> {
  auto ImportDecls = getImportDeclarations();
  if (!ImportDecls.has_value() || ImportDecls->empty())
    return {};
  std::vector<std::string> Result;
  for (auto &ImportDecl : *ImportDecls) {
    auto DependencyName = ImportDecl->getSource();
    if (!DependencyName.has_value())
      continue;
    auto Path = (*DependencyName)->getValue()->str();
    // StringLiteralExpr also contains the quotes. We strip them here.
    Result.push_back(Path.substr(1, Path.size() - 2));
  }
  return Result;
}

auto ASTTranslationUnit::debug(raw_ostream &OS) const -> void {
  OS << "ASTTranslationUnit with " << Modules.size() << " modules";
}
