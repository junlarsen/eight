//===----- XDCompiler.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/CompilerInstance.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;
using namespace xd;

namespace {
cl::opt<std::string> PackageRoot(cl::Positional, cl::desc("<package root>"),
                                 cl::init("."));
} // namespace

auto main(int argc, char **argv) -> int {
  cl::ParseCommandLineOptions(argc, argv);
  if (PackageRoot.empty()) {
    errs() << "Package not found\n";
    return 1;
  }

  auto Compiler = CompilerInstance();
  // TODO: Handle the errors
  auto RootPath = std::filesystem::canonical(
      std::filesystem::relative(std::filesystem::path(PackageRoot.data()),
                                std::filesystem::current_path()));
  auto Manifest =
      tryParsePackageManifest(RootPath, Compiler.getDiagnosticManager());
  if (auto Err = Manifest.takeError()) {
    errs() << Err;
    return 1;
  }
  Compiler.setRootPackage(RootPath, *Manifest);
  Compiler.buildTranslationUnitGraph(Compiler.getRootPackage());
  Compiler.getDiagnosticManager().debug(errs(), Compiler.getSourceManager());
  return 0;
}
