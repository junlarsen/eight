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

auto Parser::lookahead() const -> SyntaxKind {
  if (!hasNext())
    return SyntaxKind::Eof;
  return Tokens.at(Position + 1).getKind();
}

auto Parser::at(SyntaxKind SK) const -> bool { return get() == SK; }

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
  assert(hasNext() && "advance() called on parser that has reached the end");
  Events.push_back(std::make_unique<ParseAdvanceEvent>());
  Position++;
}

auto Parser::advanceWithError(StringRef Message) -> void {
  auto Checkpoint = open();
  errs() << Message << "\n";
  advance();
  close(Checkpoint, SyntaxKind::Error);
}
