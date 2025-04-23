//===----- Workspace.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_DRIVER_WORKSPACE_H
#define XD_DRIVER_WORKSPACE_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/ErrorOr.h"
#include <filesystem>

namespace xd {
class Workspace {
  std::filesystem::path WorkspaceRoot;

public:
  explicit Workspace(const std::filesystem::path &Root) : WorkspaceRoot(Root) {}

  /// Get the workspace-relative routing by routing through the root.
  ///
  /// For example, if we're starting at ~/../foo.xd, and import ./stdlib/bar.xd,
  /// we will find ~/../stdlib/bar.xd
  auto getRelativeToRootFromRelative(const std::filesystem::path &Source,
                                     const llvm::StringRef &Target) const
      -> llvm::ErrorOr<std::filesystem::path>;
};
} // namespace xd

#endif // XD_DRIVER_WORKSPACE_H
