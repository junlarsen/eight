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
enum class ParseEventKind {
  Open,
  Close,
  Advance,
};
class ParseEvent {
  ParseEventKind Kind;

public:
  ParseEvent(ParseEventKind Kind) : Kind(Kind) {}
  auto getKind() const { return Kind; }
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Open;
  }
};

class ParseOpenEvent : public ParseEvent {
  SyntaxKind SK;

public:
  ParseOpenEvent(SyntaxKind SK) : ParseEvent(ParseEventKind::Open), SK(SK) {}
  auto getSyntaxKind() const { return SK; }
  auto setSyntaxKind(SyntaxKind SK) -> void { this->SK = SK; }
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Open;
  }
};

class ParseCloseEvent : public ParseEvent {
public:
  ParseCloseEvent() : ParseEvent(ParseEventKind::Close) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Close;
  }
};

class ParseAdvanceEvent : public ParseEvent {
public:
  ParseAdvanceEvent() : ParseEvent(ParseEventKind::Advance) {}
  static bool classof(const ParseEvent *Event) {
    return Event->getKind() == ParseEventKind::Advance;
  }
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

  std::vector<Token> Tokens;
  std::vector<std::unique_ptr<ParseEvent>> Events;
  uint32_t Position = 0;

public:
  explicit Parser(DiagnosticManager &DM, std::vector<Token> Tokens)
      : DM(DM), Tokens(std::move(Tokens)) {}

  auto get() const -> SyntaxKind { return Tokens.at(Position).getKind(); }
  auto hasNext() const -> bool { return Position != Tokens.size(); }
  auto lookahead() const -> SyntaxKind;
  auto at(SyntaxKind SK) const -> bool;
  auto eat(SyntaxKind SK) -> bool;
  auto expect(SyntaxKind SK) -> void;

  auto open() -> ParseCheckpoint;
  auto close(ParseCheckpoint Checkpoint, SyntaxKind SK) -> void;
  auto advance() -> void;
  auto advanceWithError(llvm::StringRef Message) -> void;
};

} // namespace xd

#endif // XD_FRONTEND_PARSER_H
