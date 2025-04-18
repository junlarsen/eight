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

  /// Construct the Green tree from the parsed events.
  auto build() -> GreenNode;

  /// Get the tree builder's position for debug purposes.
  auto getDebugTreeBuilderComplete() const -> uint32_t {
    // The build() method will post-increment this regardless of whether there
    // is another element there or not. Thus, this is the correct comparison
    return TreeBuilderPosition == Tokens.size();
  }

  auto in(const TokenSet &TS) const -> bool { return in(TS, get()); }
  static auto in(const TokenSet &TS, SyntaxKind SK) -> bool {
    return TS[static_cast<uint64_t>(SK)];
  }

  auto parseTranslationUnit() -> void;
  auto parseDecl() -> void;
  auto parseFunctionDecl() -> void;
  auto parseFunctionTypeParameterList() -> void;
  auto parseFunctionTypeParameter() -> void;
  auto parseFunctionParameterList() -> void;
  auto parseFunctionParameter() -> void;
  auto parseFunctionReturnType() -> void;

  /// Is the parser at the start of a statement?
  ///
  /// This covers the basic keywords for statements like if/let/for, but also
  /// has to include all rules for Expr for ExprStmt.
  auto atStmtStart() const -> bool {
    static const TokenSet TS =
        (1 << SyntaxKind::KeywordLet) | (1 << SyntaxKind::KeywordIf) |
        (1 << SyntaxKind::KeywordFor) | (1 << SyntaxKind::KeywordReturn) |
        (1 << SyntaxKind::ContinueStmt) | (1 << SyntaxKind::KeywordBreak);
    return in(TS) || atExprStart();
  }

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
    static const TokenSet TS =
        (1 << SyntaxKind::Plus) | (1 << SyntaxKind::Minus) |
        (1 << SyntaxKind::Star) | (1 << SyntaxKind::Bang) |
        (1 << SyntaxKind::Ampersand);
    return in(TS);
  }

  auto atPostfixOperator() const -> bool {
    static const TokenSet TS =
        (1 << SyntaxKind::LeftParen) | (1 << SyntaxKind::Dot);
    return in(TS);
  }

  auto atInfixOperator() const -> bool {
    static const TokenSet TS =
        (1 << SyntaxKind::Plus) | (1 << SyntaxKind::Minus) |
        (1 << SyntaxKind::Star) | (1 << SyntaxKind::Slash) |
        (1 << SyntaxKind::Percent) | (1 << SyntaxKind::LeftAngleEqual) |
        (1 << SyntaxKind::RightAngleEqual) | (1 << SyntaxKind::LeftAngle) |
        (1 << SyntaxKind::RightAngle) | (1 << SyntaxKind::BangEqual) |
        (1 << SyntaxKind::EqualEqual) | (1 << SyntaxKind::PipePipe) |
        (1 << SyntaxKind::AmpersandAmpersand) | (1 << SyntaxKind::Equal);
    return in(TS);
  }

  auto atPrimaryExprStart() const -> bool {
    static const TokenSet TS =
        (1 << SyntaxKind::Identifier) | (1 << SyntaxKind::IntegerLiteral) |
        (1 << SyntaxKind::TrueLiteral) | (1 << SyntaxKind::FalseLiteral) |
        (1 << SyntaxKind::LeftParen) | (1 << SyntaxKind::KeywordNew);
    return in(TS);
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
    static const TokenSet TS =
        (1 << SyntaxKind::Plus) | (1 << SyntaxKind::Minus) |
        (1 << SyntaxKind::Bang) | (1 << SyntaxKind::Ampersand) |
        (1 << SyntaxKind::Star);
    if (in(TS, SK))
      return 6;
    llvm_unreachable("unknown syntax kind");
  }

  /// Precedence table for infix expression kinds.
  static auto getInfixPrecedence(SyntaxKind SK) -> uint32_t {
    // 1. Assignment has the lowest precedence, that way RHS is "built" first.
    if (SK == SyntaxKind::Equal)
      return 1;

    // 2. Boolean AND/OR should be evaluated after their terms
    static const TokenSet LogicalTS =
        (1 << SyntaxKind::AmpersandAmpersand) | (1 << SyntaxKind::PipePipe);
    if (in(LogicalTS, SK))
      return 2;

    // 3. Comparison operators should be evaluated after their terms too
    static const TokenSet ComparisonTS =
        (1 << SyntaxKind::EqualEqual) | (1 << SyntaxKind::BangEqual) |
        (1 << SyntaxKind::LeftAngleEqual) | (1 << SyntaxKind::RightAngleEqual) |
        (1 << SyntaxKind::LeftAngle) | (1 << SyntaxKind::RightAngle);
    if (in(ComparisonTS, SK))
      return 3;

    // 4. Additive infix operators have the least precedence
    static const TokenSet AdditiveTS =
        (1 << SyntaxKind::Plus) | (1 << SyntaxKind::Minus);
    if (in(AdditiveTS, SK))
      return 4;

    // 5. Multiplicative come after additive
    static const TokenSet MultiplicativeTS = (1 << SyntaxKind::Star) |
                                             (1 << SyntaxKind::Slash) |
                                             (1 << SyntaxKind::Percent);
    if (in(MultiplicativeTS, SK))
      return 5;
    llvm_unreachable("unknown syntax kind");
  }

  auto atTypeStart() const -> bool {
    static const TokenSet TS =
        (1 << SyntaxKind::Identifier) | (1 << SyntaxKind::Star);
    return in(TS);
  }

  auto parseType() -> void;
  auto parseNamedType() -> void;
  auto parsePointerType() -> void;
};

} // namespace xd

#endif // XD_FRONTEND_PARSER_H
