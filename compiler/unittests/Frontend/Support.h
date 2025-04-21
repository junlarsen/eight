//===----- Support.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_UNITTESTS_SUPPORT_H
#define XD_UNITTESTS_SUPPORT_H

#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/Parser.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/MemoryBuffer.h"

namespace xd::test {
struct Context {
  std::unique_ptr<llvm::MemoryBuffer> Buf;
  std::unique_ptr<DiagnosticManager> DM;
  Lexer L;
  Parser P;
};

inline auto getParser(const llvm::StringRef Input) -> std::unique_ptr<Context> {
  auto Buf = llvm::MemoryBuffer::getMemBuffer(Input);
  auto DM = std::make_unique<DiagnosticManager>();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(*DM, std::move(Lex.drain()));
  return std::make_unique<Context>(std::move(Buf), std::move(DM), Lex,
                                   std::move(P));
}
} // namespace xd::test

#endif // XD_UNITTESTS_SUPPORT_H
