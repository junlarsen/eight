//===----- TestUtils.h ----------------------------------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_UNITTESTS_FRONTEND_TESTUTILS_H
#define XD_UNITTESTS_FRONTEND_TESTUTILS_H

#include "xd/Driver/CompilerInstance.h"

namespace xd {
/// Create a compiler instance with a fake virtual package.
inline auto createTestCompilerInstance() -> CompilerInstance {
  CompilerInstance CI;
  CI.setRootPackage(std::filesystem::current_path(),
                    PackageManifest("test", "0.1.0", {"test.xd"}));
  return CI;
}
} // namespace xd

#endif
