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
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
#include <cassert>
#include <cstdint>
#include <llvm/Support/MemoryBuffer.h>

namespace xd {
/// Represents a single location in a file.
///
/// This implementation does currently not track multiple files. Makes the fine
/// assumption that input size does not exceed 4GB.
class SourceLocation {
  uint32_t Start;
  uint32_t End;

public:
  SourceLocation(uint32_t Start, uint32_t End) : Start(Start), End(End) {}
  bool operator==(const SourceLocation &Other) const {
    return Start == Other.Start && End == Other.End;
  }
};

class Token {
  SyntaxKind SK;
  llvm::SmallString<8> TextValue;

public:
  Token(SyntaxKind SK, llvm::SmallString<8> TextValue)
      : SK(SK), TextValue(TextValue) {}
  auto getKind() const { return SK; }
  auto getText() const { return TextValue; }
};

class Lexer {
  /// Pointer to the llvm::MemoryBuffer this Lexer operates on
  const char *SourcePtr;
  llvm::StringRef Source;

  /// Character offset into the source we're currently at.
  uint32_t Offset;
  /// Character offset the current token started at.
  uint32_t TokenStart;

public:
  Lexer(llvm::StringRef Source)
      : SourcePtr(Source.begin()), Source(Source), Offset(0), TokenStart(0) {}

  /// Get the current byte offset into the file
  auto getByteOffset() const -> uint32_t { return Offset; }

  auto getNextToken() -> Token;
  auto hasNext() const -> bool { return SourcePtr != Source.end(); }
  auto advance() -> char {
    assert(hasNext() &&
           "Called getNextChar on buffer that has reached the end");
    Offset += 1;
    return *SourcePtr++;
  }
  auto peek() const -> std::optional<char> {
    if (!hasNext())
      return std::nullopt;
    return *SourcePtr;
  }

  /// Drain all the tokens into a list.
  auto drain() -> std::vector<Token>;

private:
  auto getCommentToken() -> Token;
  auto getKeywordOrIdentifierToken(char Character) -> Token;
  auto getIntegerLiteralToken(char Character) -> Token;
  auto getTokenForWhitespace(char Character) -> Token;
  auto getTokenForNewline(char Character) -> Token;
  auto getTokenForBang() -> Token;
  auto getTokenForMinus() -> Token;
  auto getTokenForSlash() -> Token;
  auto getTokenForEqual() -> Token;
  auto getTokenForColon() -> Token;
  auto getTokenForAmpersand() -> Token;
  auto getTokenForPipe() -> Token;
  auto getTokenForLess() -> Token;
  auto getTokenForGreater() -> Token;

  static auto isIdentifierStart(char C) -> bool {
    return (C >= 'a' && C <= 'z') || (C >= 'A' && C <= 'Z');
  }
  static auto isIdentifierContinuation(char C) -> bool {
    return isIdentifierStart(C) || C == '_' || (C >= '0' && C <= '9');
  }
  static auto isWhitespace(char C) -> bool { return C == ' ' || C == '\t'; }
  static auto isNewline(char C) -> bool { return C == '\n' || C == '\r'; }
};
} // namespace xd

#endif // XD_FRONTEND_LEXER_H
