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
using ParseCheckpoint = uint32_t;

class Parser {
  DiagnosticManager &DM;

  std::vector<GreenToken> Tokens;
  std::vector<GreenToken> SignificantTokens;
  std::vector<std::unique_ptr<ParseEvent>> Events;
  uint32_t Position = 0;
  uint32_t TreeBuilderPosition = 0;

  auto get() const -> SyntaxKind {
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
    if (!hasNext())
      return SyntaxKind::Eof;
    return SignificantTokens.at(Position + 1).getKind();
  }
  auto hasNext() const -> bool {
    return Position < SignificantTokens.size() - 1;
  }
  auto at(SyntaxKind SK) const -> bool;
  auto eat(SyntaxKind SK) -> bool;
  auto expect(SyntaxKind SK) -> void;
  auto open() -> ParseCheckpoint;
  auto close(ParseCheckpoint Checkpoint, SyntaxKind SK) -> void;
  auto advance() -> void;
  auto reportUnexpectedAndAdvance() -> void;
  auto build() -> GreenNode;

  /// Get the tree builder's position for debug purposes.
  auto getDebugTreeBuilderComplete() const -> uint32_t {
    // The build() method will post-increment this regardless of whether there
    // is another element there or not. Therefore this is the correct comparison
    return TreeBuilderPosition == Tokens.size();
  }

  auto parseTranslationUnit() -> void;
  auto parseDecl() -> void;
  auto parseFunctionDecl() -> void;
};

} // namespace xd

#endif // XD_FRONTEND_PARSER_H
