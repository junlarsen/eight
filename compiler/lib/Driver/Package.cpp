//===----- Package.cpp ----------------------------------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/Package.h"

#include "xd/Frontend/AST.h"
#include "llvm/Support/YAMLTraits.h"

using namespace xd;
using namespace llvm;

auto Package::getAbsolutePath(const std::filesystem::path &Path) const
    -> Expected<std::filesystem::path> {
  auto Relative = PackageRoot / Path;
  std::error_code EC;
  auto Canonical = std::filesystem::canonical(Relative, EC);
  if (EC)
    return make_error<StringError>("failed to resolve path " +
                                       Relative.string() + ": " + EC.message(),
                                   inconvertibleErrorCode());
  return Canonical;
}

auto xd::tryParsePackageManifest(const std::filesystem::path &PackageRoot,
                                 DiagnosticManager &DM)
    -> Expected<PackageManifest> {
  auto ManifestPath = PackageRoot / "manifest.yml";
  if (!std::filesystem::exists(ManifestPath)) {
    return make_error<StringError>("package manifest not found",
                                   inconvertibleErrorCode());
  }
  auto Buffer = MemoryBuffer::getFile(ManifestPath.string());
  if (auto Err = Buffer.getError()) {
    return make_error<StringError>("failed to read package manifest file: " +
                                       Err.message(),
                                   inconvertibleErrorCode());
  }
  yaml::Input Input(Buffer->get()->getBuffer());
  PackageManifest Manifest;
  Input >> Manifest;
  if (auto Err = Input.error()) {
    return make_error<StringError>("failed to parse package manifest: " +
                                       Err.message(),
                                   inconvertibleErrorCode());
  }
  return Manifest;
}
