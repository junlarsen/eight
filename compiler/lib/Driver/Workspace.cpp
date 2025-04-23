//===----- Workspace.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/Workspace.h"
#include "llvm/Support/raw_ostream.h"

using namespace xd;
using namespace llvm;

auto Workspace::getRelativeToRootFromRelative(
    const std::filesystem::path &Source,
    const StringRef &Target) const -> ErrorOr<std::filesystem::path> {
  std::error_code EC;
  // TODO: Check all the error kinds
  auto WorkspaceRelativeToSource =
      canonical(absolute(relative(Source, WorkspaceRoot, EC), EC), EC)
          .parent_path();
  if (EC)
    return EC;
  return WorkspaceRelativeToSource.append(Target.str());
}
