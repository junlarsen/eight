//===----- XDCompiler.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/Parser.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include <cstdlib>

using namespace llvm;
using namespace xd;

namespace {
cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input file>"),
                               cl::init("-"));

auto getInputSource() -> std::unique_ptr<MemoryBuffer> {
  if (InputFile == "-") {
    auto Buf = MemoryBuffer::getSTDIN();
    if (auto E = Buf.getError()) {
      errs() << E.message() << "\n";
      std::exit(1);
    }
    return std::move(*Buf);
  }
  auto Buf = MemoryBuffer::getFile(InputFile);
  if (auto E = Buf.getError()) {
    errs() << E.message() << "\n";
    std::exit(1);
  }
  return std::move(*Buf);
}
} // namespace

auto main(int argc, char **argv) -> int {
  cl::ParseCommandLineOptions(argc, argv);
  auto Buf = getInputSource();
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));
  P.parseTranslationUnit();
  GreenNode Tree = P.build();
  Tree.debug(errs());

  if (DM.isEmpty())
    return 0;

  errs() << "Compiler diagnostics:" << "\n";
  for (auto &Diag : *DM.diagnostics()) {
    Diag->emit(errs());
  }
  return 1;
}
