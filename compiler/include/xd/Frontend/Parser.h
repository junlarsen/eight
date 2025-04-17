//===----- Parser.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_PARSER_H
#define XD_FRONTEND_PARSER_H

#include "xd/Frontend/Lexer.h"
#include "xd/Frontend/Syntax.h"
#include <vector>

namespace xd {
enum class ParseEventKind : uint8_t {
  Open,
  Close,
  Advance,
  Error,
};
class ParseEvent {
  ParseEventKind Kind;

public:
  explicit ParseEvent(ParseEventKind Kind) : Kind(Kind) {}
  explicit ParseEvent(ParseEvent &&) = delete;

  auto getKind() const { return Kind; }
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Open;
  }
};

class ParseOpenEvent : public ParseEvent {
  SyntaxKind SK;

public:
  explicit ParseOpenEvent(SyntaxKind SK)
      : ParseEvent(ParseEventKind::Open), SK(SK) {}
  auto getSyntaxKind() const { return SK; }
  auto setSyntaxKind(SyntaxKind SK) -> void { this->SK = SK; }
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Open;
  }
};

class ParseCloseEvent : public ParseEvent {
public:
  explicit ParseCloseEvent() : ParseEvent(ParseEventKind::Close) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Close;
  }
};

class ParseAdvanceEvent : public ParseEvent {
public:
  explicit ParseAdvanceEvent() : ParseEvent(ParseEventKind::Advance) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Advance;
  }
};

class ParseErrorEvent : public ParseEvent {
  DiagnosticID ID;

public:
  explicit ParseErrorEvent(DiagnosticID ID)
      : ParseEvent(ParseEventKind::Error), ID(ID) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Error;
  }

  auto getDiagnosticID() const -> DiagnosticID { return ID; }
};

/// Denotes a checkpoint (parser push) location.
///
/// The parser will return checkpoints upon opening that the closing counterpart
/// can decide to edit. This is useful for marking entire subsets of the token
/// stream (which effectively becomes a subtree in the complete AST) as
/// erroneous.
struct OpenCheckpoint {
  uint32_t ID;
};
struct CloseCheckpoint {
  uint32_t ID;
};

class Parser {
  DiagnosticManager &DM;

  std::vector<GreenToken> Tokens;
  std::vector<GreenToken> SignificantTokens;
  std::vector<std::unique_ptr<ParseEvent>> Events;
  uint32_t Position = 0;
  uint32_t TreeBuilderPosition = 0;

  auto get() const -> SyntaxKind {
    if (eof())
      return SyntaxKind::Eof;
    return SignificantTokens.at(Position).getKind();
  }

public:
  explicit Parser(DiagnosticManager &DM, std::vector<GreenToken> Tokens)
      : DM(DM), Tokens(std::move(Tokens)) {
    for (auto &Token : this->Tokens)
      if (!Token.isTrivia())
        SignificantTokens.push_back(Token);
  }

  auto lookahead() const -> SyntaxKind {
    if (Position + 1 >= SignificantTokens.size())
      return SyntaxKind::Eof;
    return SignificantTokens.at(Position + 1).getKind();
  }
  auto eof() const -> bool { return Position == SignificantTokens.size(); }
  auto at(SyntaxKind SK) const -> bool;
  auto eat(SyntaxKind SK) -> bool;
  auto expect(SyntaxKind SK) -> void;
  auto open() -> OpenCheckpoint;
  auto close(OpenCheckpoint Checkpoint, SyntaxKind SK) -> CloseCheckpoint;
  auto insert(CloseCheckpoint Checkpoint) -> OpenCheckpoint;
  auto advance() -> void;
  auto reportUnexpectedAndAdvance() -> void;
  auto build() -> GreenNode;

  /// Get the tree builder's position for debug purposes.
  auto getDebugTreeBuilderComplete() const -> uint32_t {
    // The build() method will post-increment this regardless of whether there
    // is another element there or not. Thus, this is the correct comparison
    return TreeBuilderPosition == Tokens.size();
  }

  auto parseTranslationUnit() -> void;
  auto parseDecl() -> void;
  auto parseFunctionDecl() -> void;
  auto parseFunctionTypeParameterList() -> void;
  auto parseFunctionTypeParameter() -> void;
  auto parseFunctionParameterList() -> void;
  auto parseFunctionParameter() -> void;
  auto parseFunctionReturnType() -> void;
  auto parseFunctionBody() -> void;

  /// Is the parser at the start of a statement?
  ///
  /// This covers the basic keywords for statements like if/let/for, but also
  /// has to include all rules for Expr for ExprStmt.
  auto atStmtStart() const -> bool {
    return at(SyntaxKind::KeywordLet) || atExprStart();
  }
  auto parseStmt() -> void;
  auto parseLetStmt() -> void;

  /// Is the parser currently at the start of an expression? This is the FIRST
  /// set of the Expr rule. Effectively this is:
  ///
  /// 1. Identifier for ReferenceExpr
  /// 2. *Literal for *LiteralExpr
  /// 3. LeftParen for GroupExpr
  /// 4. Ampersand/Star/Bang/Minus/Plus for UnaryExpr
  auto atExprStart() const -> bool {
    return atPrimaryExprStart() || atPrefixOperator();
  }
  auto atPrefixOperator() const -> bool {
    return at(SyntaxKind::Plus) || at(SyntaxKind::Minus) ||
           at(SyntaxKind::Star) || at(SyntaxKind::Bang) ||
           at(SyntaxKind::Ampersand);
  }
  auto atPostfixOperator() const -> bool {
    return at(SyntaxKind::LeftParen) || at(SyntaxKind::Dot);
  }

  auto atInfixOperator() const -> bool {
    return at(SyntaxKind::Plus) || at(SyntaxKind::Minus) ||
           at(SyntaxKind::Star) || at(SyntaxKind::Slash) ||
           at(SyntaxKind::Percent) || at(SyntaxKind::LeftAngle) ||
           at(SyntaxKind::LeftAngleEqual) || at(SyntaxKind::RightAngle) ||
           at(SyntaxKind::RightAngleEqual) || at(SyntaxKind::EqualEqual) ||
           at(SyntaxKind::BangEqual);
  }
  auto atPrimaryExprStart() const -> bool {
    return at(SyntaxKind::Identifier) || at(SyntaxKind::IntegerLiteral) ||
           at(SyntaxKind::TrueLiteral) || at(SyntaxKind::FalseLiteral) ||
           at(SyntaxKind::LeftParen) || at(SyntaxKind::KeywordNew);
  }
  auto parseExpr(uint32_t Current = 0) -> void;
  auto parsePrimaryExpr() -> CloseCheckpoint;
  auto parseIntegerLiteralExpr() -> CloseCheckpoint;
  auto parseBooleanLiteralExpr() -> CloseCheckpoint;
  auto parseGroupExpr() -> CloseCheckpoint;
  auto parseReferenceExpr() -> CloseCheckpoint;
  auto parseConstructionExpr() -> CloseCheckpoint;
  auto parseConstructionExprMember() -> void;

  /// Precedence table for prefix expression kinds.
  ///
  /// All the unary operators have higher precedence than any infix operator, so
  /// it does not actually matter here.
  static auto getPrefixPrecedence(SyntaxKind SK) -> uint32_t {
    if (SK == SyntaxKind::Plus || SK == SyntaxKind::Minus ||
        SK == SyntaxKind::Bang || SK == SyntaxKind::Ampersand ||
        SK == SyntaxKind::Star)
      return 6;
    llvm_unreachable("unknown syntax kind");
  }

  /// Precedence table for infix expression kinds.
  ///
  /// 1. Assignment has the lowest precedence, that way RHS is "built" first.
  /// 2. Boolean AND/OR should be evaluated after their terms
  /// 3. Comparison operators should be evaluated after their terms too
  /// 4. Additive infix operators have the least precedence
  /// 5. Multiplicative come after additive
  static auto getInfixPrecedence(SyntaxKind SK) -> uint32_t {
    if (SK == SyntaxKind::Equal)
      return 1;
    if (SK == SyntaxKind::AmpersandAmpersand || SK == SyntaxKind::PipePipe)
      return 2;
    if (SK == SyntaxKind::EqualEqual || SK == SyntaxKind::BangEqual ||
        SK == SyntaxKind::LeftAngle || SK == SyntaxKind::RightAngle ||
        SK == SyntaxKind::LeftAngleEqual || SK == SyntaxKind::RightAngleEqual)
      return 3;
    if (SK == SyntaxKind::Plus || SK == SyntaxKind::Minus)
      return 4;
    if (SK == SyntaxKind::Star || SK == SyntaxKind::Slash ||
        SK == SyntaxKind::Percent)
      return 5;
    llvm_unreachable("unknown syntax kind");
  }

  auto atTypeStart() const -> bool {
    return at(SyntaxKind::Identifier) || at(SyntaxKind::Star);
  }
  auto parseType() -> void;
  auto parseNamedType() -> void;
  auto parsePointerType() -> void;
};

} // namespace xd

#endif // XD_FRONTEND_PARSER_H
