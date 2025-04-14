//===----- XDTableGen.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/TableGen/Main.h"

#include <xd/TableGen/DiagnosticEmitter.h>

using namespace llvm;
using namespace xd;

namespace {
enum TableGenAction {
  GenDiagnostics,
};

cl::opt<TableGenAction>
    Action(cl::desc("tablegen action to invoke"),
           values(clEnumValN(GenDiagnostics, "gen-diagnostics",
                             "generate compiler diagnostic messages")));

auto xdTableGenMain(raw_ostream &OS, const RecordKeeper &RK) -> bool {
  switch (Action) {
  default: {
    errs() << "Unknown xd-tablegen action code";
    return true;
  }
  case GenDiagnostics: {
    auto Emitter = DiagnosticEmitter(RK);
    Emitter.emit(OS);
  }
  }
  return false;
}
} // namespace

auto main(int argc, char **argv) -> int {
  InitLLVM L(argc, argv);
  cl::ParseCommandLineOptions(argc, argv);
  return TableGenMain(argv[0], xdTableGenMain);
}
