//===----- Syntax.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Syntax module for representing red/green syntax trees.
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_SYNTAX_H
#define XD_FRONTEND_SYNTAX_H

#include "llvm/ADT/SmallString.h"
#include <cstdint>

namespace xd {
enum class SyntaxKind : uint8_t {
  Error,
  Eof,
  // Nodes
  TranslationUnit,
  FunctionParameterList,

  // Tokens
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
  Whitespace,
  Newline,

  Ampersand,
  Bang,
  Plus,
  Dot,
  Star,
  Minus,
  Slash,
  Equal,
  EqualEqual,
  BangEqual,
  Percent,

  LeftParen,
  LeftBracket,
  LeftBrace,
  LeftAngle,
  LeftAngleEqual,
  RightParen,
  RightBracket,
  RightBrace,
  RightAngle,
  RightAngleEqual,
  Semicolon,
  Colon,
  ColonColon,
  Comma,
  Arrow,
  AmpersandAmpersand,
  PipePipe,
};

class GreenToken {
  SyntaxKind SK;
  llvm::SmallString<8> TextValue;

public:
  GreenToken(SyntaxKind SK, const llvm::SmallString<8> &TextValue)
      : SK(SK), TextValue(TextValue) {}

  auto getKind() const { return SK; }
  auto getText() const { return TextValue; }

  auto isTrivia() const -> bool {
    return SK == SyntaxKind::Comment || SK == SyntaxKind::Whitespace ||
           SK == SyntaxKind::Newline;
  }
};

class GreenNode {
public:
  using ChildData = std::variant<GreenNode, GreenToken>;
  using Child = std::shared_ptr<ChildData>;

private:
  SyntaxKind SK;
  std::vector<Child> Children;

public:
  explicit GreenNode(SyntaxKind SK) : SK(SK) {}

  auto getChildren() -> std::vector<Child> & { return Children; }
  auto getKind() const { return SK; }

  auto addChild(const Child &Child) -> void { Children.push_back(Child); }
};
} // namespace xd

#endif // XD_FRONTEND_SYNTAX_H
