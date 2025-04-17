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

#include "xd/Basic/DiagnosticManager.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>

namespace xd {
enum class SyntaxKind : uint8_t {
  Error,
  Eof,
  // Nodes
  TranslationUnit,
  Function,
  FunctionTypeParameterList,
  FunctionTypeParameter,
  FunctionParameterList,
  FunctionParameter,
  FunctionReturnType,
  FunctionBody,

  Stmt,
  LetStmt,

  Expr,
  IntegerLiteralExpr,
  BooleanLiteralExpr,
  ReferenceExpr,
  GroupExpr,
  ConstantIndexExpr,
  CallExpr,
  CallExprArgumentList,
  UnaryExpr,
  BinaryExpr,
  ConstructionExpr,
  ConstructionExprMember,

  Type,
  NamedType,
  PointerType,

  // Keyword tokens
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
  // Textual tokens
  Identifier,
  IntegerLiteral,
  TrueLiteral,
  FalseLiteral,
  Comment,
  Whitespace,
  Newline,
  // Symbol tokens
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

auto getSyntaxKindName(SyntaxKind SK) -> llvm::StringRef;

/// A singular token.
///
/// This is a cheap data structure that we are fine with copying.
///
/// TODO: Intern the TextValue strings
class GreenToken {
  SyntaxKind SK;
  llvm::SmallString<8> TextValue;
  size_t Length;

public:
  GreenToken(SyntaxKind SK, const llvm::SmallString<8> &TextValue,
             size_t Length)
      : SK(SK), TextValue(TextValue), Length(Length) {}

  auto getKind() const { return SK; }
  auto getText() const { return TextValue; }
  auto getTextLength() const -> size_t { return Length; }

  auto isTrivia() const -> bool {
    return SK == SyntaxKind::Comment || SK == SyntaxKind::Whitespace ||
           SK == SyntaxKind::Newline;
  }
};

class ErrorToken {
  DiagnosticID DiagnosticID;

public:
  explicit ErrorToken(uint32_t DiagnosticID) : DiagnosticID(DiagnosticID) {}
  auto getDiagnosticID() const -> uint32_t { return DiagnosticID; }
  auto getTextLength() const -> size_t { return 0; }
  auto getKind() const -> SyntaxKind { return SyntaxKind::Error; }
};

class GreenNode {
  using GreenNodeData =
      std::variant<GreenToken, std::shared_ptr<GreenNode>, ErrorToken>;

  SyntaxKind SK;
  std::vector<GreenNodeData> Children;
  size_t Length;

public:
  explicit GreenNode(SyntaxKind SK, size_t Length) : SK(SK), Length(Length) {}

  auto getChildren() -> std::vector<GreenNodeData> & { return Children; }
  auto getKind() const { return SK; }
  auto getTextLength() const -> size_t { return Length; }

  auto setLength(size_t Length) -> void { this->Length = Length; }

  auto addChild(GreenToken Tok) -> void { Children.push_back(Tok); }
  auto addChild(const std::shared_ptr<GreenNode> &Tok) -> void {
    Children.push_back(Tok);
  }
  auto addChild(ErrorToken Tok) -> void { Children.push_back(Tok); }

  auto debug(llvm::raw_ostream &OS, size_t Indent = 0) const -> void;
};

using GreenElement = std::variant<GreenToken, GreenNode>;

class SyntaxNode {
  std::optional<std::shared_ptr<SyntaxNode>> Parent;
  GreenElement Green;
  std::vector<std::shared_ptr<SyntaxNode>> Children;
  /// How far into the file is the current node?
  ///
  /// For the root, this is zero.
  uint32_t Offset;
  uint32_t Index;

public:
  explicit SyntaxNode(std::optional<std::shared_ptr<SyntaxNode>> Parent,
                      const GreenElement &Green, uint32_t Offset,
                      uint32_t Index)
      : Parent(std::move(Parent)), Green(Green), Offset(Offset), Index(Index) {}

  auto addChild(const std::shared_ptr<SyntaxNode> &Child,
                uint32_t Index) -> void {
    Children.insert(Children.begin() + Index, Child);
  }

  /// Create a root node.
  static auto
  getRoot(const GreenElement &Green) -> std::shared_ptr<SyntaxNode> {
    return std::make_shared<SyntaxNode>(std::nullopt, Green, 0, 0);
  }

  /// Create a child node.
  static auto get(std::shared_ptr<SyntaxNode> Parent, const GreenElement &Green,
                  uint32_t Offset,
                  uint32_t Index) -> std::shared_ptr<SyntaxNode> {
    return std::make_shared<SyntaxNode>(std::move(Parent), Green, Offset,
                                        Index);
  }
};

} // namespace xd

#endif // XD_FRONTEND_SYNTAX_H
