//===----- TranslationUnit.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_TRANSLATIONUNIT_H
#define XD_FRONTEND_TRANSLATIONUNIT_H

#include "xd/Frontend/AST.h"

namespace xd {
/// Represent a translation unit at the AST/Frontend stage.
class ASTTranslationUnit {
  llvm::DenseMap<SourceFileID, std::shared_ptr<ASTModuleDecl>,
                 SourceFileID::DenseMapKeyInfo>
      Modules;

public:
  explicit ASTTranslationUnit() : Modules({}) {}

  /// Add the given module to the translation unit.
  ///
  /// It is assumed that this module has been "validated" through the module
  /// graph, meaning the file id has not been inserted here before. The function
  /// will assert this invariant on its own too.
  auto addModule(SourceFileID FileID, const std::shared_ptr<ASTModuleDecl> &M)
      -> void {
    Modules.insert(std::make_pair(FileID, M));
  }
  auto debug(llvm::raw_ostream &OS) const -> void;
};
} // namespace xd

#endif // XD_FRONTEND_TRANSLATIONUNIT_H
