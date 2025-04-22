//===----- SourceManager.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Basic/SourceManager.h"

using namespace xd;
using namespace llvm;

auto SourceManager::hasNamedSource(const StringRef &Name) const -> bool {
  return FileIDReverse.contains(Name);
}

auto SourceManager::addFileSource(
    const StringRef &Name, const std::filesystem::path &Path,
    std::unique_ptr<MemoryBuffer> Buffer) -> SourceFileID {
  auto ID = addVirtualSource(Name, std::move(Buffer));
  RealFilePaths.insert(std::make_pair(ID, Path));
  return ID;
}

auto SourceManager::addVirtualSource(const StringRef &Name,
                                     std::unique_ptr<MemoryBuffer> Buffer)
    -> SourceFileID {
  assert(!hasNamedSource(Name) && "attempted to add existing named source");
  // We offset by one so that <stdin> can always be ID 0. This does not have
  // any semantic meaning, but it means that it's always easy to know which ID
  // is pointing to stdin.
  auto ID = SourceFileID(FileNames.size() + 1);
  FileNames.insert(std::make_pair(ID, Name.str()));
  FileIDReverse.insert(std::make_pair(Name, ID));
  FileBuffers.insert(std::make_pair(ID, std::move(Buffer)));
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
