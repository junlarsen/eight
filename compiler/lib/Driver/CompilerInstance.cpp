//===----- CompilerInstance.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/CompilerInstance.h"
#include "xd/Driver/Workspace.h"
#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/ModuleGraph.h"
#include "xd/Frontend/Parser.h"
#include <string>

using namespace xd;
using namespace llvm;

auto CompilerInstance::buildModuleGraph(SourceFileID Entrypoint) const
    -> std::optional<std::unique_ptr<ASTTranslationUnit>> {
  auto TU = std::make_unique<ASTTranslationUnit>();
  auto MG = ModuleGraph();
  auto WorkQueue = SmallVector<SourceFileID, 16>();
  // Build the entire module graph, starting at the entrypoint node. This is
  // effectively BFS, with the ModuleGraph holding the list over files visited.
  WorkQueue.emplace_back(Entrypoint);
  while (!WorkQueue.empty()) {
    auto File = WorkQueue.back();
    WorkQueue.pop_back();
    // If we've already seen this file, we keep going.
    if (MG.hasModule(File))
      continue;
    // Parse the file and install it into the translation unit
    auto ModuleDecl = getModuleDeclaration(File);
    TU->addModule(File, ModuleDecl);
    auto Dependents = ModuleDecl->getReferencedDependencyPaths();
    // Visit all neighbors using BFS.
    for (auto Dep : Dependents) {
      auto SourcePath = SM->getSourcePath(File);
      assert(SourcePath.has_value() && "tried to import virtual file?");
      auto DependencyPath =
          WS->getRelativeToRootFromRelative(std::string(*SourcePath), Dep);
      if (auto E = DependencyPath.getError(); E) {
        errs() << "failed to resolve path relative to root: "
               << SourcePath->string() << ":" << E.message() << "\n";
        continue;
      }
      auto DepID = addFilesystemSource(DependencyPath->string(),
                                       DependencyPath->string());
      if (auto E = DepID.getError()) {
        // TODO: Error handling
        errs() << "could not add file " << DependencyPath->string() << ": "
               << E.message() << "\n";
        continue;
      }
      WorkQueue.emplace_back(*DepID);
    }
  }

  return std::move(TU);
}

auto CompilerInstance::addInlineSource(const StringRef &SourceName,
                                       const StringRef &Source) const
    -> SourceFileID {
  auto Buffer = MemoryBuffer::getMemBuffer(Source);
  return SM->addVirtualSource(SourceName, std::move(Buffer));
}

auto CompilerInstance::addFilesystemSource(
    const StringRef &SourceName,
    const std::filesystem::path &Path) const -> ErrorOr<SourceFileID> {
  // TODO: Maybe do some more extensive checking here on our own...
  auto Buffer = MemoryBuffer::getFile(Path.string());
  if (auto E = Buffer.getError())
    return std::move(E);
  return SM->addFileSource(SourceName, Path, std::move(Buffer.get()));
}

auto CompilerInstance::addStdinSource(std::unique_ptr<MemoryBuffer> Buf) const
    -> SourceFileID {
  return SM->addVirtualSource("<stdin>", std::move(Buf));
}

auto CompilerInstance::getSyntaxTree(SourceFileID SourceFile,
                                     const std::function<void(Parser &)> &Fn)
    const -> std::shared_ptr<SyntaxNode> {
  auto *Buf = SM->getSourceBuffer(SourceFile);
  auto Lex = Lexer(Buf->getBufferStart());
  auto Parse = Parser(*DM, std::move(Lex.drain()));
  Fn(Parse);
  auto GreenTree = Parse.build();
  return buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *DM);
}
