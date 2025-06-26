//===----- Lexer.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_LEXER_H
#define XD_FRONTEND_LEXER_H

#include "xd/Basic/DiagnosticManager.h"
#include "xd/Frontend/Syntax.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/MemoryBuffer.h"
#include <cassert>

namespace xd {
class Lexer {
  /// Pointer to the llvm::MemoryBuffer this Lexer operates on
  const char *SourcePtr;
  const llvm::StringRef &Source;

public:
  explicit Lexer(const llvm::StringRef &Source)
      : SourcePtr(Source.begin()), Source(Source) {}

  auto getNextToken() -> GreenToken;
  auto hasNext() const -> bool { return SourcePtr != Source.end(); }
  auto advance() -> char {
    assert(hasNext() &&
           "Called getNextChar on buffer that has reached the end");
    return *SourcePtr++;
  }
  auto peek() const -> std::optional<char> {
    if (!hasNext())
      return std::nullopt;
    return *SourcePtr;
  }

  /// Drain all the tokens into a list.
  auto drain() -> std::vector<GreenToken>;

private:
  auto getCommentToken() -> GreenToken;
  auto getKeywordOrIdentifierToken(char Character) -> GreenToken;
  auto getIntegerLiteralToken(char Character) -> GreenToken;
  auto getTokenForWhitespace(char Character) -> GreenToken;
  auto getTokenForNewline(char Character) -> GreenToken;
  auto getTokenForBang() -> GreenToken;
  auto getTokenForMinus() -> GreenToken;
  auto getTokenForSlash() -> GreenToken;
  auto getTokenForEqual() -> GreenToken;
  auto getTokenForColon() -> GreenToken;
  auto getTokenForAmpersand() -> GreenToken;
  auto getTokenForPipe() -> GreenToken;
  auto getTokenForLess() -> GreenToken;
  auto getTokenForGreater() -> GreenToken;

  static auto isIdentifierStart(char C) -> bool {
    return (C >= 'a' && C <= 'z') || (C >= 'A' && C <= 'Z') || C == '_';
  }
  static auto isIdentifierContinuation(char C) -> bool {
    return isIdentifierStart(C) || (C >= '0' && C <= '9');
  }
  static auto isWhitespace(char C) -> bool { return C == ' ' || C == '\t'; }
  static auto isNewline(char C) -> bool { return C == '\n' || C == '\r'; }
};
} // namespace xd

#endif // XD_FRONTEND_LEXER_H
