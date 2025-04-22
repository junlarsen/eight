//===----- CompilerInstance.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_DRIVER_COMPILERINSTANCE_H
#define XD_DRIVER_COMPILERINSTANCE_H

#include "xd/Basic/DiagnosticManager.h"
#include "xd/Basic/SourceManager.h"
#include "xd/Frontend/Parser.h"
#include "xd/Frontend/Syntax.h"
#include <memory>

namespace xd {
class CompilerInstance {
  std::unique_ptr<DiagnosticManager> DM;
  std::unique_ptr<SourceManager> SM;

public:
  explicit CompilerInstance()
      : DM(std::make_unique<DiagnosticManager>()),
        SM(std::make_unique<SourceManager>()) {}

  auto hasDiagnostics() const -> bool { return !DM->isEmpty(); }
  auto diagnostics() const { return DM->diagnostics(); }

  /// Add an inline source snippet to the compiler instance.
  ///
  /// This is useful for tests primarily, but the functionality is general
  /// enough to warrant public API.
  auto addInlineSource(const llvm::StringRef &SourceName,
                       const llvm::StringRef &Source) const -> SourceFileID;

  auto
  addSource(const llvm::StringRef &SourceName,
            std::unique_ptr<llvm::MemoryBuffer> Source) const -> SourceFileID {
    return SM->addNamedSource(SourceName, std::move(Source));
  }

  /// Get the red tree for the given source file.
  ///
  /// This is primarily useful for access to debug tools during development of
  /// the compiler itself.
  auto getSyntaxTree(SourceFileID SourceFile,
                     const std::function<void(Parser &)> &Fn) const
      -> std::shared_ptr<SyntaxNode>;

  /// Get the red tree for the given source file.
  ///
  /// Will attempt to parse the source file as a translation unit. This can be
  /// changed with the other overload of getSyntaxTree.
  auto
  getSyntaxTree(SourceFileID SourceFile) const -> std::shared_ptr<SyntaxNode> {
    return getSyntaxTree(SourceFile,
                         [](Parser &P) { P.parseTranslationUnit(); });
  }
};
} // namespace xd

#endif // XD_DRIVER_COMPILERINSTANCE_H
