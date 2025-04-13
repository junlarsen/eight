//===----- Lexer.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LEXER_H
#define LEXER_H

#include "Syntax.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/StringRef.h"
#include <cassert>
#include <cstdint>

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

class Lexer {
  /// Pointer to the llvm::MemoryBuffer this Lexer operates on
  const char *SourcePtr;
  llvm::StringRef Source;

  /// Character offset into the source we're currently at.
  uint32_t Offset;
  /// Character offset the current token started at.
  uint32_t TokenStart;

  std::string TextValue;

public:
  explicit Lexer(llvm::StringRef Source)
      : SourcePtr(Source.begin()), Source(Source), Offset(0), TokenStart(0) {}

  /// Get the newly built token's source location.
  auto getSourceLocation() const -> SourceLocation {
    return SourceLocation(TokenStart, Offset);
  }

  /// Get the current identifier from the Lexer state, if present.
  ///
  /// Should only be called when you have some knowledge that the value will
  /// be present, such as after reading a Identifier token kind.
  auto getTextValue() -> std::string { return TextValue; }

  auto getNextToken() -> SyntaxKind;
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

private:
  auto getCommentToken() -> SyntaxKind;
  auto getKeywordOrIdentifierToken(char Character) -> SyntaxKind;
  auto getIntegerLiteralToken(char Character) -> SyntaxKind;
  auto getTokenForWhitespace(char Character) -> SyntaxKind;
  auto getTokenForNewline(char Character) -> SyntaxKind;
  auto getTokenForBang() -> SyntaxKind;
  auto getTokenForMinus() -> SyntaxKind;
  auto getTokenForSlash() -> SyntaxKind;
  auto getTokenForEqual() -> SyntaxKind;
  auto getTokenForColon() -> SyntaxKind;
  auto getTokenForAmpersand() -> SyntaxKind;
  auto getTokenForPipe() -> SyntaxKind;
  auto getTokenForLess() -> SyntaxKind;
  auto getTokenForGreater() -> SyntaxKind;

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

#endif // LEXER_H
