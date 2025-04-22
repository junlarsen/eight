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
  return FilesInverse.contains(Name);
}

auto SourceManager::addNamedSource(const StringRef &Name,
                                   std::unique_ptr<MemoryBuffer> Buffer)
    -> SourceFileID {
  assert(!hasNamedSource(Name) && "attempted to add existing named source");
  // We offset by one so that <stdin> can always be ID 0. This does not have
  // any semantic meaning, but it means that it's always easy to know which ID
  // is pointing to stdin.
  auto ID = SourceFileID(Files.size() + 1);
  Files.insert(std::make_pair(ID, Name.str()));
  FilesInverse.insert(std::make_pair(Name, ID));
  FileBuffers.insert(std::make_pair(ID, std::move(Buffer)));
  // Sanity check to ensure size invariant is maintained
  assert(Files.size() == FilesInverse.size() && "size of maps have diverged");
  return ID;
}

auto SourceManager::getSourceBuffer(SourceFileID SourceFile) const
    -> MemoryBuffer * {
  assert(Files.contains(SourceFile) &&
         "source file with given id does not exist");
  return FileBuffers.at(SourceFile).get();
}
