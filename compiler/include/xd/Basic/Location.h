//===----- Location.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_BASIC_LOCATION_H
#define XD_BASIC_LOCATION_H

#include <cstdint>

namespace xd {
/// Represents a single location in a file.
///
/// This implementation does currently not track multiple files. Makes the fine
/// assumption that input size does not exceed 4GB.
class SourceLocation {
  uint32_t Start;
  uint32_t End;

public:
  SourceLocation(uint32_t Start, uint32_t End) : Start(Start), End(End) {}
  bool operator==(const SourceLocation &Other) const {
    return Start == Other.Start && End == Other.End;
  }
};
} // namespace xd

#endif // XD_BASIC_LOCATION_H
