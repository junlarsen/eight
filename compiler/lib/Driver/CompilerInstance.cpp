//===----- CompilerInstance.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/CompilerInstance.h"
#include "xd/Driver/Package.h"
#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/Parser.h"
#include <string>

using namespace xd;
using namespace llvm;

auto CompilerInstance::buildTranslationUnitGraph(const Package &P) -> void {
  auto TU = std::make_shared<ASTTranslationUnit>();
  for (auto &M : P.getModules()) {
    // This is a help check in case somebody listed the same file multiple times
    auto DepID = findFilesystemSource(M);
    if (DepID.has_value()) {
      // TODO: Report this as a compiler diagnostic
      errs() << "Duplicate module entry source for: " << M << "\n";
      continue;
    }
    // We try to add the source file to the source manager, and then try parse
    // its contents as a separate module which will be mapped into an AST
    // translation unit.
    auto Source = addFilesystemSource(M, P.getRoot() / M);
    if (auto E = Source.getError()) {
      // TODO: Report this as a compiler diagnostic
      errs() << "Failed to add source file " << M << ": " << E.message()
             << "\n";
      continue;
    }
    auto SourceFileID = Source.get();
    auto ModuleDecl = getModuleDeclaration(SourceFileID);
    TU->addModule(SourceFileID, ModuleDecl);
    TranslationUnits.emplace_back(TU);
  }
}

auto CompilerInstance::getRootPackage() const -> Package & {
  assert(RootPackage != nullptr && "Root package is not set");
  return *RootPackage;
}

auto CompilerInstance::setRootPackage(const std::filesystem::path &Root,
                                      PackageManifest MF) -> void {
  assert(RootPackage == nullptr && "Attempted to re-set the root package");
  RootPackage = std::make_unique<Package>(Root, std::move(MF));
}

auto CompilerInstance::addInlineSource(const StringRef &SourceName,
                                       const StringRef &Source) const
    -> SourceFileID {
  auto Buffer = MemoryBuffer::getMemBuffer(Source);
  return SM->addVirtualSource(SourceName, std::move(Buffer));
}

auto CompilerInstance::addFilesystemSource(
    const StringRef &SourceName, const std::filesystem::path &Path) const
    -> ErrorOr<SourceFileID> {
  // TODO: Maybe do some more extensive checking here on our own...
  auto Buffer = MemoryBuffer::getFile(Path.string());
  if (auto E = Buffer.getError())
    return std::move(E);
  return SM->addFileSource(SourceName, Path, std::move(Buffer.get()));
}

auto CompilerInstance::findFilesystemSource(const StringRef &SourceName) const
    -> std::optional<SourceFileID> {
  return SM->findNamedSource(SourceName);
}

auto CompilerInstance::addStdinSource(std::unique_ptr<MemoryBuffer> Buf) const
    -> SourceFileID {
  return SM->addVirtualSource("<stdin>", std::move(Buf));
}

auto CompilerInstance::getSyntaxTree(
    SourceFileID SourceFile, const std::function<void(Parser &)> &Fn) const
    -> std::shared_ptr<SyntaxNode> {
  auto *Buf = SM->getSourceBuffer(SourceFile);
  auto Lex = Lexer(Buf->getBufferStart());
  auto Parse = Parser(*DM, std::move(Lex.drain()));
  Fn(Parse);
  auto GreenTree = Parse.build();
  return buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *DM,
                         SourceFile);
}
