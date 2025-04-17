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
  Events.push_back(std::make_unique<ParseAdvanceEvent>());
  if (hasNext())
    Position++;
}

auto Parser::advanceWithError(StringRef Message) -> void {
  auto Checkpoint = open();
  errs() << Message << "\n";
  advance();
  close(Checkpoint, SyntaxKind::Error);
}

auto Parser::build() -> GreenNode {
  std::vector<GreenNode> Stack;
  // Pop the first event off the stack because it's a close event
  assert(Events.size() > 0 && "Tried to build tree with zero events in tree");
  Events.pop_back();
  for (auto &Event : Events) {
    if (const auto OE = dyn_cast<ParseOpenEvent>(Event)) {
      // An open event simply pushes a new tree onto the stack
      Stack.push_back(GreenNode(OE->getSyntaxKind()));
    } else if (const auto AE = dyn_cast<ParseAdvanceEvent>(Event)) {
      // Advancing will push the token kind onto the current element's children
      // list.
      while (TreeBuilderPosition < Tokens.size() - 1) {
        auto &Tok = Tokens.at(TreeBuilderPosition);
        TreeBuilderPosition++;
        // As long as we're hitting trivia nodes, we just add them to the green
        // node.
        if (Tok.isTrivia()) {
          Stack.at(Stack.size() - 1).addChild(Tok);
          continue;
        }
        // This is the token that the parser saw (i.e., the one after all trivia
        // skipped).
        Stack.at(Stack.size() - 1).addChild(Tok);
        break;
      }
    } else if (const auto CE = dyn_cast<ParseCloseEvent>(Event)) {
      // Closing events simply pop the top element of the deque and puts it into
      // the top again
      GreenNode Subtree = std::move(Stack.back());
      Stack.erase(Stack.end() - 1);
      Stack.at(Stack.size() - 1).addChild(std::make_shared<GreenNode>(Subtree));
    }
  }
  assert(Stack.size() == 1 &&
         "Stack was not left with a single element after building");
  GreenNode Root = std::move(Stack.front());
  // We also drain any remaining trivia tokens and put them into the root here.
  while (TreeBuilderPosition < Tokens.size() - 1) {
    auto &Tok = Tokens.at(TreeBuilderPosition);
    assert(Tok.isTrivia() && "Dangling token was not a trivia token");
    TreeBuilderPosition++;
    Root.addChild(Tok);
  }
  return Root;
}
