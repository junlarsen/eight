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
#include <cassert>
#include <vector>

using namespace llvm;
using namespace xd;

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
  assert(Lex.hasNext() && "Called advance() on a parser whose lexer is empty");
  Lex.advance();
  Events.push_back(std::make_unique<ParseAdvanceEvent>());
}
