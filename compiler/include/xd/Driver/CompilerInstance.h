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
#include "xd/Driver/Package.h"
#include "xd/Frontend/AST.h"
#include "xd/Frontend/Parser.h"
#include "xd/Frontend/Syntax.h"
#include "xd/Frontend/TranslationUnit.h"
#include <filesystem>

namespace xd {
class CompilerInstance {
  std::unique_ptr<DiagnosticManager> DM;
  std::unique_ptr<SourceManager> SM;
  std::unique_ptr<Package> RootPackage;

public:
  explicit CompilerInstance()
      : DM(std::make_unique<DiagnosticManager>()),
        SM(std::make_unique<SourceManager>()), RootPackage(nullptr) {}

  /// Get the root package of the compiler instance.
  ///
  /// This function asserts that the root package is set, so it should only be
  /// called if the root package is guaranteed to be set.
  auto getRootPackage() const -> Package &;

  /// Set the root package of the compiler instance. This can only be done once
  auto setRootPackage(const std::filesystem::path &Root, PackageManifest MF)
      -> void;

  auto getSourceManager() const -> SourceManager & { return *SM; }
  auto getDiagnosticManager() const -> DiagnosticManager & { return *DM; }

  auto hasDiagnostics() const -> bool { return !DM->isEmpty(); }
  auto diagnostics() const { return DM->diagnostics(); }

  /// Add an inline source snippet to the compiler instance.
  ///
  /// This is useful for tests primarily, but the functionality is general
  /// enough to warrant public API.
  auto addInlineSource(const llvm::StringRef &SourceName,
                       const llvm::StringRef &Source) const -> SourceFileID;

  /// Add the given filesystem path to the source manager.
  auto addFilesystemSource(const llvm::StringRef &SourceName,
                           const std::filesystem::path &Path) const
      -> llvm::ErrorOr<SourceFileID>;

  auto findFilesystemSource(const llvm::StringRef &SourceName) const
      -> std::optional<SourceFileID>;

  /// Add STDIN as a source.
  auto addStdinSource(std::unique_ptr<llvm::MemoryBuffer> Buf) const
      -> SourceFileID;

  /// Completely traverse the module graph taking the given file as the
  /// entrypoint.
  ///
  /// This will return nullopt if the module graph detects a cycle in the
  /// dependency graph.
  auto buildRootModuleGraph(SourceFileID Entrypoint) const
      -> std::unique_ptr<ASTTranslationUnit> {
    return buildModuleGraph(Entrypoint, getRootPackage());
  }
  auto buildModuleGraph(SourceFileID Entrypoint, Package P) const
      -> std::unique_ptr<ASTTranslationUnit>;

  /// Get the red tree for the given source file.
  ///
  /// This is primarily useful for access to debug tools during development of
  /// the compiler itself.
  auto getSyntaxTree(SourceFileID SourceFile,
                     const std::function<void(Parser &)> &Fn) const
      -> std::shared_ptr<SyntaxNode>;

  /// Get the red tree for the given source file.
  ///
  /// Will attempt to parse the source file as a module. This can be changed
  /// with the other overload of getSyntaxTree.
  auto getSyntaxTree(SourceFileID SourceFile) const
      -> std::shared_ptr<SyntaxNode> {
    return getSyntaxTree(SourceFile, [](Parser &P) { P.parseModuleDecl(); });
  }

  /// Get the module declaration for a source file.
  auto getModuleDeclaration(SourceFileID SourceFile) const
      -> std::shared_ptr<ASTModuleDecl> {
    auto ST = getSyntaxTree(SourceFile);
    auto Module = ASTModuleDecl::cast(ST);
    assert(Module.has_value() && "getSyntaxTree did not return a ModuleDecl");
    return *Module;
  }
};
} // namespace xd

#endif // XD_DRIVER_COMPILERINSTANCE_H
