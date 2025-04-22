//===----- SourceManager.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_BASIC_SOURCEMANAGER_H
#define XD_BASIC_SOURCEMANAGER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/MemoryBuffer.h"
#include <cstdint>

namespace xd {
/// Represent the reference to a single input source file.
class SourceFileID {
  uint8_t ID;

public:
  /// DenseMap Key info type
  struct DenseMapKeyInfo {
    static SourceFileID getEmptyKey() {
      return SourceFileID(std::numeric_limits<uint8_t>::max());
    };
    static SourceFileID getTombstoneKey() {
      return SourceFileID(std::numeric_limits<uint8_t>::max());
    }
    static unsigned getHashValue(const SourceFileID &Val) { return Val.ID; }
    static bool isEqual(const SourceFileID &LHS, const SourceFileID &RHS) {
      return LHS.ID == RHS.ID;
    }
  };

  explicit SourceFileID(uint8_t ID) : ID(ID) {}

  /// Cast to uint32_t.
  operator uint32_t() const { return ID; }
};

class SourceManager {
  llvm::StringMap<SourceFileID> FilesInverse;
  llvm::DenseMap<SourceFileID, std::string, SourceFileID::DenseMapKeyInfo>
      Files;
  llvm::DenseMap<SourceFileID, std::unique_ptr<llvm::MemoryBuffer>,
                 SourceFileID::DenseMapKeyInfo>
      FileBuffers;

public:
  explicit SourceManager() {}
  /// Add a named source to the source manager.
  ///
  /// This takes ownership of the memory buffer.
  auto
  addNamedSource(const llvm::StringRef &Name,
                 std::unique_ptr<llvm::MemoryBuffer> Buffer) -> SourceFileID;

  auto hasNamedSource(const llvm::StringRef &Name) const -> bool;

  /// Get the given memory buffer.
  ///
  /// The caller must ensure the buffer exist, otherwise an assertion will fail
  /// here.
  auto getSourceBuffer(SourceFileID SourceFile) const -> llvm::MemoryBuffer *;
};
} // namespace xd

#endif // XD_BASIC_SOURCEMANAGER_H
