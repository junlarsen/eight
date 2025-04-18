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
  uint32_t Length;

public:
  explicit ParseErrorEvent(DiagnosticID ID, uint32_t Length)
      : ParseEvent(ParseEventKind::Error), ID(ID), Length(Length) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Error;
  }

  auto getLength() const { return Length; }
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
    return SignificantTokens.at(Position).getSyntaxKind();
  }

  auto getTokenLength() const -> uint32_t {
    if (eof())
      return 0;
    return SignificantTokens.at(Position).getTextLength();
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
    return SignificantTokens.at(Position + 1).getSyntaxKind();
  }
  auto eof() const -> bool { return Position == SignificantTokens.size(); }
  auto at(SyntaxKind SK) const -> bool;
  auto eat(SyntaxKind SK) -> bool;
  auto expect(SyntaxKind SK) -> void;
  auto open() -> OpenCheckpoint;
  auto close(OpenCheckpoint Checkpoint, SyntaxKind SK) -> CloseCheckpoint;
  auto insert(CloseCheckpoint Checkpoint) -> OpenCheckpoint;
  auto advance() -> void;

  /// Construct a diagnostic in-place, and advance the parser by one token.
  template <class T, class... Args>
  auto report(uint32_t Len, Args &&...A) -> void {
    auto Checkpoint = open();
    DiagnosticID ID = DM.report<T>(std::forward<Args>(A)...);
    auto Event = std::make_unique<ParseErrorEvent>(ID, Len);
    Events.push_back(std::move(Event));
    advance();
    close(Checkpoint, SyntaxKind::Error);
  }

  /// Construct the Green tree from the parsed events.
  auto build() -> GreenNode;

  /// Get the tree builder's position for debug purposes.
  auto getDebugTreeBuilderComplete() const -> uint32_t {
    // The build() method will post-increment this regardless of whether there
    // is another element there or not. Thus, this is the correct comparison
    return TreeBuilderPosition == Tokens.size();
  }

  auto at(const TokenSet &TS) const -> bool { return in(TS, get()); }
  static auto in(const TokenSet &TS, SyntaxKind SK) -> bool {
    return TS[static_cast<uint64_t>(SK)];
  }

  auto atDeclStart() const -> bool { return at(TSDeclStart); }
  auto atExprStart() const -> bool {
    return atPrimaryExprStart() || atPrefixOperator();
  }
  auto atPrefixOperator() const -> bool { return at(TSPrefixOperator); }
  auto atPostfixOperator() const -> bool { return at(TSPostfixOperator); }
  auto atInfixOperator() const -> bool { return at(TSInfixOperator); }
  auto atPrimaryExprStart() const -> bool {
    return at(TSPrimaryExpressionStart);
  }
  auto atTypeStart() const -> bool { return at(TSTypeStart); }
  auto atStmtStart() const -> bool {
    return at(TSStatementStart) || atExprStart();
  }

  auto parseTranslationUnit() -> void;
  auto parseDecl() -> void;
  auto parseFunctionDecl() -> void;
  auto parseFunctionTypeParameterList() -> void;
  auto parseFunctionTypeParameter() -> void;
  auto parseFunctionParameterList() -> void;
  auto parseFunctionParameter() -> void;
  auto parseFunctionReturnType() -> void;
  auto parseIntrinsicTypeDecl() -> void;
  auto parseStructDecl() -> void;
  auto parseStructMemberList() -> void;
  auto parseStructMember() -> void;

  auto parseStmt() -> void;
  auto parseBlock(SyntaxKind SK) -> void;
  auto parseLetStmt() -> void;
  auto parseIfStmt() -> void;
  auto parseForStmt() -> void;
  auto parseForInitializer() -> void;
  auto parseReturnStmt() -> void;
  auto parseExprStmt() -> void;
  auto parseContinueStmt() -> void;
  auto parseBreakStmt() -> void;

  auto parseExpr(uint32_t Current = 0) -> void;
  auto parsePrimaryExpr() -> CloseCheckpoint;
  auto parseIntegerLiteralExpr() -> CloseCheckpoint;
  auto parseBooleanLiteralExpr() -> CloseCheckpoint;
  auto parseGroupExpr() -> CloseCheckpoint;
  auto parseReferenceExpr() -> CloseCheckpoint;
  auto parseConstructionExpr() -> CloseCheckpoint;
  auto parseConstructionExprMember() -> void;

  auto parseType() -> void;
  auto parseNamedType() -> void;
  auto parsePointerType() -> void;

  /// Precedence table for prefix expression kinds.
  ///
  /// All the unary operators have higher precedence than any infix operator, so
  /// it does not actually matter here.
  static auto getPrefixPrecedence(SyntaxKind SK) -> uint32_t {
    if (in(TSPrefixOperator, SK))
      return 6;
    llvm_unreachable("unknown syntax kind");
  }

  /// Precedence table for infix expression kinds.
  static auto getInfixPrecedence(SyntaxKind SK) -> uint32_t {
    if (in(TSInfixEqualOperator, SK))
      return 1;
    if (in(TSInfixLogicalOperator, SK))
      return 2;
    if (in(TSInfixComparisonOperator, SK))
      return 3;
    if (in(TSInfixAdditiveOperator, SK))
      return 4;
    if (in(TSInfixMultiplicativeOperator, SK))
      return 5;
    llvm_unreachable("unknown syntax kind");
  }

  static auto getUnaryExprSyntaxKind(SyntaxKind SK) -> SyntaxKind {
    if (SK == SyntaxKind::Plus)
      return SyntaxKind::UnaryPlusExpr;
    if (SK == SyntaxKind::Minus)
      return SyntaxKind::UnaryMinusExpr;
    if (SK == SyntaxKind::Bang)
      return SyntaxKind::UnaryNotExpr;
    if (SK == SyntaxKind::Ampersand)
      return SyntaxKind::UnaryAddrOfExpr;
    if (SK == SyntaxKind::Star)
      return SyntaxKind::UnaryDerefExpr;
    llvm_unreachable("unknown syntax kind");
  }

  static auto getBinaryExprSyntaxKind(SyntaxKind SK) -> SyntaxKind {
    if (SK == SyntaxKind::Equal)
      return SyntaxKind::BinaryAssignExpr;
    if (SK == SyntaxKind::AmpersandAmpersand)
      return SyntaxKind::BinaryLogicalAndExpr;
    if (SK == SyntaxKind::PipePipe)
      return SyntaxKind::BinaryLogicalOrExpr;
    if (SK == SyntaxKind::EqualEqual)
      return SyntaxKind::BinaryEqualityExpr;
    if (SK == SyntaxKind::BangEqual)
      return SyntaxKind::BinaryInequalityExpr;
    if (SK == SyntaxKind::LeftAngle)
      return SyntaxKind::BinaryLessThanExpr;
    if (SK == SyntaxKind::LeftAngleEqual)
      return SyntaxKind::BinaryLessThanEqualExpr;
    if (SK == SyntaxKind::RightAngle)
      return SyntaxKind::BinaryGreaterThanExpr;
    if (SK == SyntaxKind::RightAngleEqual)
      return SyntaxKind::BinaryGreaterThanEqualExpr;
    if (SK == SyntaxKind::Plus)
      return SyntaxKind::BinaryAddExpr;
    if (SK == SyntaxKind::Minus)
      return SyntaxKind::BinarySubExpr;
    if (SK == SyntaxKind::Star)
      return SyntaxKind::BinaryMulExpr;
    if (SK == SyntaxKind::Slash)
      return SyntaxKind::BinaryDivExpr;
    if (SK == SyntaxKind::Percent)
      return SyntaxKind::BinaryModulusExpr;
    llvm_unreachable("unknown syntax kind");
  }
};

} // namespace xd

#endif // XD_FRONTEND_PARSER_H
