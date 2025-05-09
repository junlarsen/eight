//===----- XDCompiler.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/CompilerInstance.h"
#include "xd/Frontend/ModuleGraph.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;
using namespace xd;

namespace {
cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input file>"),
                               cl::init("-"));

cl::opt<bool> EmitModuleGraph("emit-module-graph",
                              cl::desc("emit the module graph as graphviz dot"),
                              cl::init(false));
} // namespace

auto main(int argc, char **argv) -> int {
  cl::ParseCommandLineOptions(argc, argv);
  auto CI = CompilerInstance();
  if (InputFile == "-") {
    errs() << "stdin input not supported at this time\n";
    return 1;
  }
  auto EntryID =
      CI.addFilesystemSource(std::string(InputFile), std::string(InputFile));
  if (auto EC = EntryID.getError()) {
    errs() << "Error reading input file '" << EC.message() << "'\n";
    return 1;
  }
  auto TU = CI.buildModuleGraph(*EntryID);
  if (!TU.has_value()) {
    errs() << "Error building TU\n";
    return 1;
  }
  (*TU)->debug(errs());
  (*TU)->getModuleGraph().debug(errs(), CI.getSourceManager());

  return 0;
}
