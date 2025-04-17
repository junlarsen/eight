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
#include <fcntl.h>
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
  auto CurrentSK = get();
  auto ID = DM.report<UnexpectedTokenDiagnostic>(getSyntaxKindName(CurrentSK));
  auto Event = std::make_unique<ParseErrorEvent>(ID);
  Events.push_back(std::move(Event));
}

auto Parser::open() -> OpenCheckpoint {
  auto Checkpoint = Events.size();
  auto Event = std::make_unique<ParseOpenEvent>(SyntaxKind::Error);
  Events.push_back(std::move(Event));
  return OpenCheckpoint(Checkpoint);
}

auto Parser::close(OpenCheckpoint Checkpoint,
                   SyntaxKind SK) -> CloseCheckpoint {
  auto &E = Events.at(Checkpoint.ID);
  assert(
      isa<ParseOpenEvent>(*E) &&
      "Attempted to modify OpenEvent, but target event was not an OpenEvent");
  auto &OpenEvent = cast<ParseOpenEvent>(*E);
  OpenEvent.setSyntaxKind(SK);
  Events.push_back(std::make_unique<ParseCloseEvent>());
  return CloseCheckpoint(Checkpoint.ID);
}

auto Parser::insert(CloseCheckpoint Checkpoint) -> OpenCheckpoint {
  auto OpenCP = OpenCheckpoint(Checkpoint.ID);
  auto Event = std::make_unique<ParseOpenEvent>(SyntaxKind::Error);
  // TODO: Consider using a linked list to avoid O(N) worst-case here
  Events.insert(Events.begin() + Checkpoint.ID, std::move(Event));
  return OpenCheckpoint(OpenCP);
}

auto Parser::advance() -> void {
  Events.push_back(std::make_unique<ParseAdvanceEvent>());
  if (!eof())
    Position++;
}

auto Parser::reportUnexpectedAndAdvance() -> void {
  auto Checkpoint = open();
  auto CurrentSK = get();
  auto ID = DM.report<UnexpectedTokenDiagnostic>(getSyntaxKindName(CurrentSK));
  auto Event = std::make_unique<ParseErrorEvent>(ID);
  Events.push_back(std::move(Event));
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
      // An open event simply pushes a new tree onto the stack. So far, we don't
      // know what the length will be, so we initialize it to zero, and update
      // as we go.
      Stack.push_back(GreenNode(OE->getSyntaxKind(), 0));
    } else if (const auto AE = dyn_cast<ParseAdvanceEvent>(Event)) {
      // Advancing will push the token kind onto the current element's children
      // list.
      while (TreeBuilderPosition < Tokens.size()) {
        auto &Tok = Tokens.at(TreeBuilderPosition++);
        // As long as we're hitting trivia nodes, we just add them to the green
        // node.
        if (Tok.isTrivia()) {
          Stack.at(Stack.size() - 1).addChild(Tok);
          continue;
        }
        Stack.at(Stack.size() - 1).addChild(Tok);
        break;
      }
    } else if (const auto CE = dyn_cast<ParseCloseEvent>(Event)) {
      // Closing events simply pop the top element of the deque and puts it into
      // the top again
      GreenNode Subtree = std::move(Stack.back());
      Stack.erase(Stack.end() - 1);
      // Compute the length of node by summing all its children.
      size_t Sum = 0;
      for (auto &Child : Subtree.getChildren()) {
        if (std::holds_alternative<GreenToken>(Child)) {
          auto &Tok = std::get<GreenToken>(Child);
          Sum += Tok.getTextLength();
        } else if (std::holds_alternative<std::shared_ptr<GreenNode>>(Child)) {
          auto &Node = std::get<std::shared_ptr<GreenNode>>(Child);
          // This is relatively cheap, because although it might seem recurse
          // down all child nodes here, it ends up not being the case, because
          // we've already computed and store the length of the children.
          Sum += Node->getTextLength();
        }
      }
      Subtree.setLength(Sum);
      GreenNode &Head = Stack.at(Stack.size() - 1);
      Head.addChild(std::make_shared<GreenNode>(Subtree));
    } else if (const auto EE = dyn_cast<ParseErrorEvent>(Event)) {
      auto Tok = ErrorToken(EE->getDiagnosticID());
      Stack.at(Stack.size() - 1).addChild(Tok);
    } else {
      llvm_unreachable("unexpected event kind");
    }
  }
  assert(Stack.size() == 1 &&
         "Stack was not left with a single element after building");
  GreenNode Root = std::move(Stack.front());
  // We also drain any remaining tokens and put them into the root here. The
  // tokens here can be of any kind.
  while (TreeBuilderPosition < Tokens.size()) {
    auto &Tok = Tokens.at(TreeBuilderPosition++);
    Root.addChild(Tok);
  }

  // Next, because we never close the Root event, we also have to calculate the
  // sum down here. It is probably not worth extracting into its own function.
  size_t Sum = 0;
  for (auto &Child : Root.getChildren()) {
    if (std::holds_alternative<GreenToken>(Child)) {
      auto &Tok = std::get<GreenToken>(Child);
      Sum += Tok.getTextLength();
    } else if (std::holds_alternative<std::shared_ptr<GreenNode>>(Child)) {
      auto &Node = std::get<std::shared_ptr<GreenNode>>(Child);
      Sum += Node->getTextLength();
    }
  }
  Root.setLength(Sum);
  return Root;
}

auto Parser::parseTranslationUnit() -> void {
  auto TU = open();
  while (!eof()) {
    parseDecl();
  }
  close(TU, SyntaxKind::TranslationUnit);
}

auto Parser::parseDecl() -> void {
  switch (get()) {
  case SyntaxKind::KeywordFn:
    return parseFunctionDecl();
  default:
    // The top-level parser has to try to advance, otherwise the parser will
    // just loop forever.
    reportUnexpectedAndAdvance();
  }
}

auto Parser::parseFunctionDecl() -> void {
  assert(at(SyntaxKind::KeywordFn) && "called parseFunctionDecl without 'fn'");
  auto C = open();
  expect(SyntaxKind::KeywordFn);
  expect(SyntaxKind::Identifier);
  if (at(SyntaxKind::LeftBracket)) {
    parseFunctionTypeParameterList();
  }
  if (at(SyntaxKind::LeftParen)) {
    parseFunctionParameterList();
  }
  if (eat(SyntaxKind::Arrow)) {
    parseFunctionReturnType();
  }
  if (at(SyntaxKind::LeftBrace)) {
    parseFunctionBody();
  }
  close(C, SyntaxKind::Function);
}

auto Parser::parseFunctionTypeParameterList() -> void {
  assert(at(SyntaxKind::LeftBracket) &&
         "called parseFunctionTypeParameterList without '['");
  auto C = open();
  expect(SyntaxKind::LeftBracket);
  while (!eof() && !at(SyntaxKind::RightBracket)) {
    if (at(SyntaxKind::Identifier)) {
      parseFunctionTypeParameter();
    } else {
      break;
    }
  }
  expect(SyntaxKind::RightBracket);
  close(C, SyntaxKind::FunctionTypeParameterList);
}

auto Parser::parseFunctionTypeParameter() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseFunctionParameterList without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  if (!at(SyntaxKind::RightAngle)) {
    eat(SyntaxKind::Comma);
  }
  close(C, SyntaxKind::FunctionTypeParameter);
}

auto Parser::parseFunctionParameterList() -> void {
  assert(at(SyntaxKind::LeftParen) &&
         "called parseFunctionParameterList without '('");
  auto C = open();
  expect(SyntaxKind::LeftParen);
  while (!eof() && !at(SyntaxKind::RightParen)) {
    if (at(SyntaxKind::Identifier)) {
      parseFunctionParameter();
    } else {
      break;
    }
  }
  expect(SyntaxKind::RightParen);
  close(C, SyntaxKind::FunctionParameterList);
}

auto Parser::parseFunctionParameter() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseFunctionParameter without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  expect(SyntaxKind::Colon);
  parseType();
  if (!at(SyntaxKind::RightParen)) {
    eat(SyntaxKind::Comma);
  }
  close(C, SyntaxKind::FunctionParameter);
}

auto Parser::parseFunctionReturnType() -> void {
  auto C = open();
  if (at(SyntaxKind::Identifier) || at(SyntaxKind::Star)) {
    parseType();
  }
  close(C, SyntaxKind::FunctionReturnType);
}

auto Parser::parseFunctionBody() -> void {
  assert(at(SyntaxKind::LeftBrace) && "called parseFunctionBody without '{'");
  auto C = open();
  expect(SyntaxKind::LeftBrace);
  while (!eof() && !at(SyntaxKind::RightBrace)) {
    if (atStmtStart()) {
      parseStmt();
    } else {
      break;
    }
  }
  expect(SyntaxKind::RightBrace);
  close(C, SyntaxKind::FunctionBody);
}

auto Parser::parseStmt() -> void {
  assert(atStmtStart() && "called parseStmt without being at stmt start");
  auto C = open();
  if (at(SyntaxKind::KeywordLet)) {
    parseLetStmt();
  }
  close(C, SyntaxKind::Stmt);
}
auto Parser::parseLetStmt() -> void {
  assert(at(SyntaxKind::KeywordLet) && "called parseLetStmt without 'let'");
  auto C = open();
  expect(SyntaxKind::KeywordLet);
  expect(SyntaxKind::Identifier);
  if (eat(SyntaxKind::Colon)) {
    parseType();
  }
  expect(SyntaxKind::Equal);
  if (atExprStart()) {
    parseExpr();
  }
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::LetStmt);
}

auto Parser::parseExpr(uint32_t Current) -> void {
  auto Tok = get();
  CloseCheckpoint LHS;
  // If we have a basic atom (expr, ref, or group), we have already found the
  // LHS.
  if (atPrimaryExprStart()) {
    LHS = parsePrimaryExpr();
  } else if (atPrefixOperator()) {
    // Then the current looked-at token MUST be a prefix operator. We then go
    // grab that as the LHS instead.
    auto New = getPrefixPrecedence(Tok);
    auto C = open();
    advance();
    if (atExprStart())
      parseExpr(New);
    LHS = close(C, SyntaxKind::UnaryExpr);
  } else {
    llvm_unreachable("LHS was meant to be guaranteed to be assigned here");
  }

  // At this point, we are guaranteed to have an LHS, and we can try crawl for
  // postfix tokens.
  while (!eof() && (atPostfixOperator() || atInfixOperator()) &&
         Current <= getInfixPrecedence(get())) {
    // We parse postfix operators in a loop until there are no more
    while (atPostfixOperator()) {
      auto C = insert(LHS);
      switch (get()) {
      case SyntaxKind::LeftParen: {
        auto CC = open();
        expect(SyntaxKind::LeftParen);
        while (!eof() && !at(SyntaxKind::RightParen)) {
          if (atExprStart())
            parseExpr();
          if (!at(SyntaxKind::RightParen)) {
            expect(SyntaxKind::Comma);
          }
        }
        expect(SyntaxKind::RightParen);
        close(CC, SyntaxKind::CallExprArgumentList);
        LHS = close(C, SyntaxKind::CallExpr);
      } break;
      case SyntaxKind::Dot: {
        expect(SyntaxKind::Dot);
        expect(SyntaxKind::Identifier);
        LHS = close(C, SyntaxKind::ConstantIndexExpr);
      } break;
      default:
        llvm_unreachable("cannot reach unhandled case");
      }
    }

    // Finally, we consider if there is a infix expression to be built here.
    auto Tok = get();
    if (!atInfixOperator())
      return;
    auto C = insert(LHS);
    advance();
    auto NextPrecedence = getInfixPrecedence(Tok);
    if (atExprStart())
      parseExpr(NextPrecedence);
    LHS = close(C, SyntaxKind::BinaryExpr);
  }
}

auto Parser::parsePrimaryExpr() -> CloseCheckpoint {
  assert(atPrimaryExprStart() &&
         "called parseGroupOrLiteralExpr without group or literal start");
  switch (get()) {
  case SyntaxKind::IntegerLiteral:
    return parseIntegerLiteralExpr();
  case SyntaxKind::TrueLiteral:
  case SyntaxKind::FalseLiteral:
    return parseBooleanLiteralExpr();
  case SyntaxKind::Identifier:
    return parseReferenceExpr();
  case SyntaxKind::LeftParen:
    return parseGroupExpr();
  case SyntaxKind::KeywordNew:
    return parseConstructionExpr();
  default:
    llvm_unreachable("unreachable");
  }
}

auto Parser::parseIntegerLiteralExpr() -> CloseCheckpoint {
  assert(at(SyntaxKind::IntegerLiteral) &&
         "called parseIntegerLiteralExpr without <integer literal>");
  auto C = open();
  expect(SyntaxKind::IntegerLiteral);
  return close(C, SyntaxKind::IntegerLiteral);
}

auto Parser::parseBooleanLiteralExpr() -> CloseCheckpoint {
  assert((at(SyntaxKind::TrueLiteral) || at(SyntaxKind::FalseLiteral)) &&
         "called parseBooleanLiteral without 'true' or 'false'");
  auto C = open();
  advance();
  return close(C, SyntaxKind::BooleanLiteralExpr);
}

auto Parser::parseGroupExpr() -> CloseCheckpoint {
  assert(at(SyntaxKind::LeftParen) && "called parseGroupExpr without '('");
  auto C = open();
  expect(SyntaxKind::LeftParen);
  if (atExprStart())
    parseExpr();
  expect(SyntaxKind::RightParen);
  return close(C, SyntaxKind::GroupExpr);
}

auto Parser::parseReferenceExpr() -> CloseCheckpoint {
  assert(at(SyntaxKind::Identifier) &&
         "called parseReferenceExpr without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  return close(C, SyntaxKind::ReferenceExpr);
}

auto Parser::parseConstructionExpr() -> CloseCheckpoint {
  assert(at(SyntaxKind::KeywordNew) &&
         "called parseConstructionExpr without 'new'");
  auto C = open();
  expect(SyntaxKind::KeywordNew);
  if (atTypeStart())
    parseType();
  if (eat(SyntaxKind::LeftBrace)) {
    while (!eof() && !at(SyntaxKind::RightBrace)) {
      if (at(SyntaxKind::Identifier)) {
        parseConstructionExprMember();
      }
    }
    expect(SyntaxKind::RightBrace);
  }
  return close(C, SyntaxKind::ConstructionExpr);
}

auto Parser::parseConstructionExprMember() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseConstructionExprMember without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  expect(SyntaxKind::Equal);
  if (atExprStart())
    parseExpr();
  if (!at(SyntaxKind::RightBrace))
    eat(SyntaxKind::Comma);
  close(C, SyntaxKind::ConstructionExprMember);
}

auto Parser::parseType() -> void {
  assert(atTypeStart() && "called parseType without '*' or <identifier>");
  auto C = open();
  if (at(SyntaxKind::Identifier)) {
    parseNamedType();
  } else if (at(SyntaxKind::Star)) {
    parsePointerType();
  }
  close(C, SyntaxKind::Type);
}

auto Parser::parseNamedType() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseNamedType without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  close(C, SyntaxKind::NamedType);
}

auto Parser::parsePointerType() -> void {
  assert(at(SyntaxKind::Star) && "called parsePointerType without '*'");
  auto C = open();
  expect(SyntaxKind::Star);
  if (atTypeStart()) {
    parseType();
  }
  close(C, SyntaxKind::PointerType);
}
