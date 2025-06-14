//===----- Package.h - XD Package manifests -------------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_DRIVER_PACKAGE_H
#define XD_DRIVER_PACKAGE_H

#include "xd/Basic/DiagnosticManager.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ErrorOr.h"
#include "llvm/Support/YAMLTraits.h"
#include <filesystem>

namespace xd {
/// The manifest definition for the package.
///
/// The manifest is defined in a file named `manifest.yml` which declares the
/// name, entrypoint, version, and other metadata about the package.
class PackageManifest {
  std::string Package;
  std::string Version;
  std::string Entrypoint;

  // Give LLVM YAML traits access to assigning the private members.
  friend class llvm::yaml::MappingTraits<PackageManifest>;

public:
  explicit PackageManifest(std::string Package, std::string Version,
                           std::string Entrypoint)
      : Package(std::move(Package)), Version(std::move(Version)),
        Entrypoint(std::move(Entrypoint)) {}
  explicit PackageManifest() = default;

  auto getPackage() const -> const std::string & { return Package; }
  auto getVersion() const -> const std::string & { return Version; }
  auto getEntrypoint() const -> const std::string & { return Entrypoint; }
};

/// A single package used by a program.
class Package {
  std::filesystem::path PackageRoot;
  PackageManifest Manifest;

public:
  explicit Package(const std::filesystem::path &Root, PackageManifest Manifest)
      : PackageRoot(Root), Manifest(Manifest) {}

  auto getRoot() const -> const std::filesystem::path & { return PackageRoot; }
  auto getEntrypoint() const -> const std::string & {
    return Manifest.getEntrypoint();
  }
  auto getName() const -> const std::string & { return Manifest.getPackage(); }
  auto getVersion() const -> const std::string & {
    return Manifest.getVersion();
  }

  /// Get the absolute path of a file, relative to this package's root.
  auto getAbsolutePath(const std::filesystem::path &Path) const
      -> llvm::Expected<std::filesystem::path>;
};

auto tryParsePackageManifest(const std::filesystem::path &PackageRoot,
                             DiagnosticManager &DM)
    -> llvm::Expected<PackageManifest>;
} // namespace xd

template <> struct llvm::yaml::MappingTraits<xd::PackageManifest> {
  static void mapping(IO &IO, xd::PackageManifest &Manifest) {
    IO.mapRequired("package", Manifest.Package);
    IO.mapRequired("version", Manifest.Version);
    IO.mapRequired("entrypoint", Manifest.Entrypoint);
  }
};

#endif
