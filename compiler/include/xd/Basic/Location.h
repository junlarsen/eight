//===----- Location.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_BASIC_LOCATION_H
#define XD_BASIC_LOCATION_H

#include "xd/Basic/SourceManager.h"
#include <cstdint>

namespace xd {
/// Represents a single location in a file.
///
/// This implementation does currently not track multiple files. Makes the fine
/// assumption that input size does not exceed 4GB.
class SourceLocation {
  uint32_t Start;
  uint32_t End;
  SourceFileID FileID;

public:
  SourceLocation(uint32_t Start, uint32_t End, SourceFileID FileID)
      : Start(Start), End(End), FileID(FileID) {}
  bool operator==(const SourceLocation &Other) const {
    return Start == Other.Start && End == Other.End && FileID == Other.FileID;
  }

  auto getStart() const { return Start; }
  auto getEnd() const { return End; }
  auto getFileID() const { return FileID; }
};
} // namespace xd

#endif // XD_BASIC_LOCATION_H
