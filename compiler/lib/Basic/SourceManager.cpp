//===----- SourceManager.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"

using namespace xd;
using namespace llvm;

auto SourceManager::hasNamedSource(const StringRef &Name) const -> bool {
  return FileIDReverse.contains(Name);
}

auto SourceManager::findNamedSource(const StringRef &Name) const
    -> std::optional<SourceFileID> {
  if (FileIDReverse.contains(Name))
    return FileIDReverse.at(Name);
  return std::nullopt;
}

auto SourceManager::addFileSource(const StringRef &Name,
                                  const std::filesystem::path &Path,
                                  std::unique_ptr<MemoryBuffer> Buffer,
                                  const StringRef &Package,
                                  const StringRef &PackagePath)
    -> SourceFileID {
  auto ID = addVirtualSource(Name, std::move(Buffer), Package, PackagePath);
  RealFilePaths.insert(std::make_pair(ID, Path));
  return ID;
}

auto SourceManager::addVirtualSource(const StringRef &Name,
                                     std::unique_ptr<MemoryBuffer> Buffer,
                                     const StringRef &Package,
                                     const StringRef &PackagePath)
    -> SourceFileID {
  assert(!hasNamedSource(Name) && "attempted to add existing named source");
  // We offset by one so that <stdin> can always be ID 0. This does not have
  // any semantic meaning, but it means that it's always easy to know which ID
  // is pointing to stdin.
  auto ID = SourceFileID(FileNames.size() + 1);
  FileNames.insert(std::make_pair(ID, Name.str()));
  FileIDReverse.insert(std::make_pair(Name, ID));
  FileBuffers.insert(std::make_pair(ID, std::move(Buffer)));
  Packages.insert(std::make_pair(ID, Package.str()));
  PackagePaths.insert(std::make_pair(ID, PackagePath.str()));
  // Sanity check to ensure size invariant is maintained
  assert(FileNames.size() == FileIDReverse.size() &&
         "size of maps have diverged");
  return ID;
}

auto SourceManager::getSourceBuffer(SourceFileID SourceFile) const
    -> MemoryBuffer * {
  assert(FileNames.contains(SourceFile) &&
         "source file with given id does not exist");
  return FileBuffers.at(SourceFile).get();
}

auto SourceManager::getSourcePath(SourceFileID SourceFile) const
    -> std::optional<std::filesystem::path> {
  if (RealFilePaths.contains(SourceFile))
    return RealFilePaths.at(SourceFile);
  return std::nullopt;
}

auto SourceManager::debug(raw_ostream &OS) const -> void {
  OS << "SourceManager with " << FileNames.size() << " files:\n";
  for (const auto &[ID, Name] : FileNames) {
    auto Package = Packages.at(ID);
    auto PackagePath = PackagePaths.at(ID);
    OS << "  " << Name << " (ID: " << ID
       << ", Package: " << Package << ", Path: " << PackagePath << ")\n";
  }
}
