//===----- Parser.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Parser.h"
#include "xd/Frontend/AST.h"
#include "xd/Frontend/Syntax.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

using namespace llvm;
using namespace xd;

auto Parser::lookahead() -> Token {
  // If there is no lookahead value, we try to get it from the lexer, or we
  // return the EOF if the lexer has reached the end of its input.
  if (!Lookahead.has_value()) {
    if (Lex.hasNext())
      Lookahead = Lex.getNextToken();
    else
      Lookahead = Token(SyntaxKind::Eof, StringRef(""));
  }
  // Lookahead is guaranteed to not be nullopt here.
  return *Lookahead;
}

auto Parser::at(SyntaxKind SK) -> bool { return get().getKind() == SK; }

auto Parser::eat(SyntaxKind SK) -> bool {
  if (at(SK)) {
    advance();
    return true;
  }
  return false;
}

auto Parser::expect(SyntaxKind SK) -> void {
  if (eat(SK))
    return;
  errs() << "expected syntaxkind: " << static_cast<uint8_t>(SK) << "\n";
}

auto Parser::open() -> ParseCheckpoint {
  auto Checkpoint = Events.size();
  auto Event = std::make_unique<ParseOpenEvent>(SyntaxKind::Error);
  Events.push_back(std::move(Event));
  return Checkpoint;
}

auto Parser::close(ParseCheckpoint Checkpoint, SyntaxKind SK) -> void {
  auto TargetEvent = *Events.at(Checkpoint);
  assert(
      isa<ParseOpenEvent>(TargetEvent) &&
      "Attempted to modify OpenEvent, but target event was not an OpenEvent");
  auto *OpenEvent = cast<ParseOpenEvent>(&TargetEvent);
  OpenEvent->setSyntaxKind(SK);
  Events.push_back(std::make_unique<ParseCloseEvent>());
}

auto Parser::advance() -> void {
  // If we have attempted to peek the future token, we can rewind here.
  if (Lookahead.has_value()) {
    Current = Lookahead.value();
    Lookahead = std::nullopt;
    return;
  }
  // Reset lookahead here, as we move one token ahead.
  Lookahead = std::nullopt;
  Events.push_back(std::make_unique<ParseAdvanceEvent>());
  if (Lex.hasNext()) {
    Current = Lex.getNextToken();
    return;
  }
  // If the lexer does not have any more tokens, then we give the Eof token.
  Current = Token(SyntaxKind::Eof, StringRef(""));
}

auto Parser::advanceWithError(StringRef Message) -> void {
  auto Checkpoint = open();
  errs() << Message << "\n";
  advance();
  close(Checkpoint, SyntaxKind::Error);
}
