//===----- Lexer.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LEXER_H
#define LEXER_H

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

enum class TokenKind : uint8_t {
  KeywordStruct,
  KeywordLet,
  KeywordFn,
  KeywordIntrinsicFn,
  KeywordIntrinsicType,
  KeywordTrait,
  KeywordInstance,
  KeywordIf,
  KeywordElse,
  KeywordReturn,
  KeywordBreak,
  KeywordContinue,
  KeywordFor,
  KeywordNew,

  Identifier,
  IntegerLiteral,
  TrueLiteral,
  FalseLiteral,
  Comment,

  Ampersand,
  Bang,
  Plus,
  Dot,
  Star,
  Minus,
  Slash,
  Equal,
  EqualEqual,
  LessEqual,
  GreaterEqual,
  BangEqual,
  Percent,

  LeftParen,
  LeftBracket,
  LeftBrace,
  LeftAngle,
  RightParen,
  RightBracket,
  RightBrace,
  RightAngle,

  Semicolon,
  Colon,
  ColonColon,
  Comma,
  Arrow,
  LogicalAnd,
  LogicalOr,

  EndOfFile,
  Error,
};

class Lexer {
  /// Pointer to the llvm::MemoryBuffer this Lexer operates on
  const char *SourcePtr;
  llvm::StringRef Source;

  /// Character offset into the source we're currently at.
  uint32_t Offset;
  /// Character offset the current token started at.
  uint32_t TokenStart;

  llvm::APInt IntVal;
  std::string Identifier;

public:
  explicit Lexer(llvm::StringRef Source)
      : SourcePtr(Source.begin()), Source(Source), Offset(0), TokenStart(0) {}

  /// Get the newly built token's source location.
  auto getSourceLocation() const -> SourceLocation {
    return SourceLocation(TokenStart, Offset);
  }

  /// Get the current integer value from the Lexer state, if present.
  ///
  /// Should only be called when you have some knowledge that the value will
  /// be present, such as after locating a IntegerLiteral token kind.
  ///
  /// Booleans are also returned in this APInt as 1 or 0.
  auto getIntVal() -> llvm::APInt { return IntVal; }

  /// Get the current identifier from the Lexer state, if present.
  ///
  /// Should only be called when you have some knowledge that the value will
  /// be present, such as after reading a Identifier token kind.
  auto getIdentifier() -> std::string { return Identifier; }

  auto getNextToken() -> TokenKind;
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
  auto getCommentToken() -> TokenKind;
  auto getKeywordOrIdentifierToken(char Character) -> TokenKind;
  auto getIntegerLiteralToken(char Character) -> TokenKind;
  auto getTokenForBang() -> TokenKind;
  auto getTokenForMinus() -> TokenKind;
  auto getTokenForSlash() -> TokenKind;
  auto getTokenForEqual() -> TokenKind;
  auto getTokenForColon() -> TokenKind;
  auto getTokenForAmpersand() -> TokenKind;
  auto getTokenForPipe() -> TokenKind;
  auto getTokenForLess() -> TokenKind;
  auto getTokenForGreater() -> TokenKind;
};
} // namespace xd

#endif // LEXER_H
