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
  if (CurrentSK == SyntaxKind::Eof) {
    auto ID = DM.report<UnexpectedEndOfFileDiagnostic>();
    auto Event = std::make_unique<ParseErrorEvent>(getTokenLength(), ID);
    Events.push_back(std::move(Event));
    return;
  }
  auto ID = DM.report<UnexpectedTokenDiagnostic>(getSyntaxKindName(CurrentSK));
  auto Event = std::make_unique<ParseErrorEvent>(getTokenLength(), ID);
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
          Stack.at(Stack.size() - 1)
              .addChild(std::make_shared<GreenToken>(Tok));
          continue;
        }
        Stack.at(Stack.size() - 1).addChild(std::make_shared<GreenToken>(Tok));
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
        // Skip error tokens, as they are a duplicate length of the token that
        // caused the error to be reported.
        if (isa<GreenError>(Child.get()))
          continue;
        Sum += Child->getTextLength();
      }
      Subtree.setLength(Sum);
      GreenNode &Head = Stack.at(Stack.size() - 1);
      Head.addChild(std::make_shared<GreenNode>(Subtree));
    } else if (const auto EE = dyn_cast<ParseErrorEvent>(Event)) {
      auto Err = GreenError(EE->getDiagnosticID(), EE->getLength());
      Stack.at(Stack.size() - 1).addChild(std::make_unique<GreenError>(Err));
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
    Root.addChild(std::make_shared<GreenToken>(Tok));
  }

  // Next, because we never close the Root event, we also have to calculate the
  // sum down here. It is probably not worth extracting into its own function.
  size_t Sum = 0;
  for (const auto &Child : Root.getChildren()) {
    if (isa<GreenError>(Child.get()))
      continue;
    Sum += Child->getTextLength();
  }
  Root.setLength(Sum);
  return Root;
}

auto Parser::parseTranslationUnit() -> void {
  auto TU = open();
  while (!eof()) {
    if (atDeclStart()) {
      parseDecl();
    } else {
      // The top-level parser has to try to advance, otherwise the parser will
      // just loop forever.
      report<UnexpectedTokenDiagnostic>(getTokenLength(),
                                        getSyntaxKindName(get()));
    }
  }
  close(TU, SyntaxKind::TranslationUnit);
}

auto Parser::parseDecl() -> void {
  assert(atDeclStart() && "called parseDecl without decl");
  switch (get()) {
  case SyntaxKind::KeywordFn:
  case SyntaxKind::KeywordIntrinsicFn:
    parseFunctionDecl();
    break;
  case SyntaxKind::KeywordIntrinsicType:
    parseIntrinsicTypeDecl();
    break;
  case SyntaxKind::KeywordStruct:
    parseStructDecl();
    break;
  case SyntaxKind::KeywordTrait:
    parseTraitDecl();
    break;
  case SyntaxKind::KeywordInstance:
    parseInstanceDecl();
    break;
  default:
    llvm_unreachable("disparity between atDeclStart() and kinds in switch");
  }
}

auto Parser::parseFunctionDecl() -> void {
  assert(at(SyntaxKind::KeywordFn) ||
         at(SyntaxKind::KeywordIntrinsicFn) &&
             "called parseFunctionDecl without 'fn' or 'intrinsic_fn'");
  auto C = open();
  bool IsIntrinsic = at(SyntaxKind::KeywordIntrinsicFn);
  advance();
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
  // We only try parsing a body if we are in an actual function (i.e., not
  // intrinsic)
  if (IsIntrinsic) {
    expect(SyntaxKind::Semicolon);
  } else {
    if (at(SyntaxKind::LeftBrace))
      parseBlock(SyntaxKind::FunctionBody);
  }
  // Pick the node type based on whether we parsed an intrinsic function or not
  close(C, IsIntrinsic ? SyntaxKind::IntrinsicFunction : SyntaxKind::Function);
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
      if (at(TSFunctionTypeParameterListRecovery)) {
        break;
      }
      report<ExpectedFunctionTypeParameterDiagnostic>(getTokenLength(),
                                                      getSyntaxKindName(get()));
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
      if (at(TSFunctionParameterListRecovery)) {
        break;
      }
      report<ExpectedFunctionParameterDiagnostic>(getTokenLength(),
                                                  getSyntaxKindName(get()));
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
  if (atTypeStart()) {
    parseType();
  }
  close(C, SyntaxKind::FunctionReturnType);
}

auto Parser::parseIntrinsicTypeDecl() -> void {
  assert(at(SyntaxKind::KeywordIntrinsicType) &&
         "called parseIntrinsicTypeDecl without 'intrinsic_type'");
  auto C = open();
  expect(SyntaxKind::KeywordIntrinsicType);
  expect(SyntaxKind::Identifier);
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::IntrinsicType);
}

auto Parser::parseStructDecl() -> void {
  assert(at(SyntaxKind::KeywordStruct) &&
         "called parseStructDecl without 'struct'");
  auto C = open();
  expect(SyntaxKind::KeywordStruct);
  expect(SyntaxKind::Identifier);
  if (at(SyntaxKind::LeftBrace))
    parseStructMemberList();
  close(C, SyntaxKind::Struct);
}

auto Parser::parseStructMemberList() -> void {
  assert(at(SyntaxKind::LeftBrace) &&
         "called parseStructMemberList without '{'");
  auto C = open();
  expect(SyntaxKind::LeftBrace);
  while (!eof() && !at(SyntaxKind::RightBrace)) {
    if (at(SyntaxKind::Identifier)) {
      parseStructMember();
    } else {
      if (at(TSStructMemberListRecovery)) {
        break;
      }
      report<ExpectedStructMemberDiagnostic>(getTokenLength(),
                                             getSyntaxKindName(get()));
    }
    if (!at(SyntaxKind::RightBrace))
      eat(SyntaxKind::Comma);
  }
  expect(SyntaxKind::RightBrace);
  close(C, SyntaxKind::StructMemberList);
}

auto Parser::parseStructMember() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseStructMember without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  expect(SyntaxKind::Colon);
  if (atTypeStart())
    parseType();
  close(C, SyntaxKind::StructMember);
}

auto Parser::parseTraitDecl() -> void {
  assert(at(SyntaxKind::KeywordTrait) &&
         "called parseTraitDecl without 'trait'");
  auto C = open();
  expect(SyntaxKind::KeywordTrait);
  expect(SyntaxKind::Identifier);
  if (at(SyntaxKind::LeftBracket))
    parseTraitTypeParameterList();
  if (at(SyntaxKind::LeftBrace))
    parseTraitMemberList();
  close(C, SyntaxKind::Trait);
}

auto Parser::parseTraitTypeParameterList() -> void {
  assert(at(SyntaxKind::LeftBracket) &&
         "called parseTraitTypeParameterList without '['");
  auto C = open();
  expect(SyntaxKind::LeftBracket);
  while (!eof() && !at(SyntaxKind::RightBracket)) {
    if (at(SyntaxKind::Identifier)) {
      parseTraitTypeParameter();
    } else {
      if (at(TSTraitTypeParameterListRecovery)) {
        break;
      }
      report<ExpectedTraitTypeParameterDiagnostic>(getTokenLength(),
                                                   getSyntaxKindName(get()));
    }
    if (!at(SyntaxKind::RightBrace))
      eat(SyntaxKind::Comma);
  }
  expect(SyntaxKind::RightBracket);
  close(C, SyntaxKind::TraitTypeParameterList);
}

auto Parser::parseTraitTypeParameter() -> void {
  assert(at(SyntaxKind::Identifier) &&
         "called parseTraitTypeParameter without <identifier>");
  auto C = open();
  expect(SyntaxKind::Identifier);
  close(C, SyntaxKind::TraitTypeParameter);
}

auto Parser::parseTraitMemberList() -> void {
  assert(at(SyntaxKind::LeftBrace) &&
         "called parseTraitMemberList without '{'");
  auto C = open();
  expect(SyntaxKind::LeftBrace);
  while (!eof() && !at(SyntaxKind::RightBrace)) {
    if (atTraitMemberStart()) {
      switch (get()) {
      case SyntaxKind::KeywordFn:
        // parseTraitFunctionMember will handle the only case. This switch is
        // mostly for possible future features such as associated constants or
        // types.
        parseTraitFunctionMember();
        break;
      default:
        llvm_unreachable(
            "disparity between atTraitMemberStart and above switch cases");
      }
    } else {
      if (at(TSTraitMemberListRecovery)) {
        break;
      }
      report<ExpectedTraitMemberDiagnostic>(getTokenLength(),
                                            getSyntaxKindName(get()));
    }
  }
  expect(SyntaxKind::RightBrace);
  close(C, SyntaxKind::TraitMemberList);
}

auto Parser::parseTraitFunctionMember() -> void {
  assert(at(SyntaxKind::KeywordFn) &&
         "called parseTraitFunctionMember without 'fn' or 'intrinsic_fn'");
  auto C = open();
  advance();
  expect(SyntaxKind::Identifier);
  // This function can simply re-use the same parsing rules that we apply to
  // functions. It might look a bit off in the syntax tree, but the parse rules
  // are identical.
  if (at(SyntaxKind::LeftBracket))
    parseFunctionTypeParameterList();
  if (at(SyntaxKind::LeftParen))
    parseFunctionParameterList();
  if (eat(SyntaxKind::Arrow))
    parseFunctionReturnType();
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::TraitFunctionMember);
}

auto Parser::parseInstanceDecl() -> void {
  assert(at(SyntaxKind::KeywordInstance) &&
         "called parseInstanceDecl without 'instance'");
  auto C = open();
  expect(SyntaxKind::KeywordInstance);
  expect(SyntaxKind::Identifier);
  if (at(SyntaxKind::LeftBracket))
    parseInstanceTypeArgumentList();
  expect(SyntaxKind::KeywordFor);
  if (atTypeStart())
    parseType();
  if (at(SyntaxKind::LeftBrace))
    parseInstanceMemberList();
  close(C, SyntaxKind::Instance);
}

auto Parser::parseInstanceTypeArgumentList() -> void {
  assert(at(SyntaxKind::LeftBracket) &&
         "called parseInstanceTypeArgument without '['");
  auto C = open();
  expect(SyntaxKind::LeftBracket);
  while (!eof() && !at(SyntaxKind::RightBracket)) {
    if (atTypeStart()) {
      parseType();
    } else {
      if (at(TSInstanceTypeArgumentListRecovery)) {
        break;
      }
      report<ExpectedInstanceTypeArgumentDiagnostic>(getTokenLength(),
                                                     getSyntaxKindName(get()));
    }
    if (!at(SyntaxKind::RightBracket))
      eat(SyntaxKind::Comma);
  }
  expect(SyntaxKind::RightBracket);
  close(C, SyntaxKind::InstanceTypeArgumentList);
}

auto Parser::parseInstanceMemberList() -> void {
  assert(at(SyntaxKind::LeftBrace) &&
         "called parseInstanceMemberList without '{'");
  auto C = open();
  expect(SyntaxKind::LeftBrace);
  while (!eof() && !at(SyntaxKind::RightBrace)) {
    if (atInstanceMemberStart()) {
      switch (get()) {
      case SyntaxKind::KeywordFn:
      case SyntaxKind::KeywordIntrinsicFn:
        parseFunctionDecl();
        break;
      default:
        llvm_unreachable("disparity between atInstanceMemberStart and above");
      }
    } else {
      if (at(TSInstanceMemberListRecovery)) {
        break;
      }
      report<ExpectedInstanceMemberDiagnostic>(getTokenLength(),
                                               getSyntaxKindName(get()));
    }
  }
  expect(SyntaxKind::RightBrace);
  close(C, SyntaxKind::InstanceMemberList);
}

auto Parser::parseStmt() -> void {
  assert(atStmtStart() && "called parseStmt without being at stmt start");
  switch (get()) {
  case SyntaxKind::KeywordLet:
    parseLetStmt();
    break;
  case SyntaxKind::KeywordIf:
    parseIfStmt();
    break;
  case SyntaxKind::KeywordReturn:
    parseReturnStmt();
    break;
  case SyntaxKind::KeywordFor:
    parseForStmt();
    break;
  case SyntaxKind::KeywordBreak:
    parseBreakStmt();
    break;
  case SyntaxKind::KeywordContinue:
    parseContinueStmt();
    break;
  default:
    parseExprStmt();
  }
}

auto Parser::parseBlock(SyntaxKind SK) -> void {
  assert(at(SyntaxKind::LeftBrace) && "called parseNamedBlock without '{'");
  auto C = open();
  expect(SyntaxKind::LeftBrace);
  while (!eof() && !at(SyntaxKind::RightBrace)) {
    if (atStmtStart()) {
      parseStmt();
    } else {
      if (at(TSBlockRecovery)) {
        break;
      }
    }
  }
  expect(SyntaxKind::RightBrace);
  close(C, SK);
}

auto Parser::parseLetStmt() -> void {
  assert(at(SyntaxKind::KeywordLet) && "called parseLetStmt without 'let'");
  auto C = open();
  expect(SyntaxKind::KeywordLet);
  expect(SyntaxKind::Identifier);
  if (eat(SyntaxKind::Colon)) {
    if (atTypeStart())
      parseType();
  }
  expect(SyntaxKind::Equal);
  if (atExprStart()) {
    parseExpr();
  }
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::LetStmt);
}

auto Parser::parseIfStmt() -> void {
  assert(at(SyntaxKind::KeywordIf) && "called parseIfStmt without 'if'");
  auto C = open();
  expect(SyntaxKind::KeywordIf);
  expect(SyntaxKind::LeftParen);
  if (atExprStart()) {
    parseExpr();
  }
  expect(SyntaxKind::RightParen);
  if (at(SyntaxKind::LeftBrace))
    parseBlock(SyntaxKind::IfThenBody);
  if (eat(SyntaxKind::KeywordElse)) {
    if (at(SyntaxKind::LeftBrace)) {
      parseBlock(SyntaxKind::IfElseBody);
    }
  }
  close(C, SyntaxKind::IfStmt);
}

auto Parser::parseForStmt() -> void {
  assert(at(SyntaxKind::KeywordFor) && "called parseForStmt without 'for'");
  auto C = open();
  expect(SyntaxKind::KeywordFor);
  if (at(SyntaxKind::LeftParen)) {
    expect(SyntaxKind::LeftParen);
    if (at(SyntaxKind::KeywordLet))
      parseForInitializer();
    expect(SyntaxKind::Semicolon);
    if (atExprStart()) {
      auto CC = open();
      parseExpr();
      close(CC, SyntaxKind::ForCondition);
    }
    expect(SyntaxKind::Semicolon);
    if (atExprStart()) {
      auto CC = open();
      parseExpr();
      close(CC, SyntaxKind::ForIncrement);
    }
    expect(SyntaxKind::RightParen);
  }
  if (at(SyntaxKind::LeftBrace))
    parseBlock(SyntaxKind::ForBody);
  close(C, SyntaxKind::ForStmt);
}

auto Parser::parseForInitializer() -> void {
  assert(at(SyntaxKind::KeywordLet) &&
         "called parseForInitializer without 'let'");
  auto C = open();
  expect(SyntaxKind::KeywordLet);
  expect(SyntaxKind::Identifier);
  if (eat(SyntaxKind::Colon))
    parseType();
  expect(SyntaxKind::Equal);
  if (atExprStart())
    parseExpr();
  close(C, SyntaxKind::ForInitializer);
}

auto Parser::parseBreakStmt() -> void {
  assert(at(SyntaxKind::KeywordBreak) &&
         "called parseBreakStmt without 'break'");
  auto C = open();
  expect(SyntaxKind::KeywordBreak);
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::BreakStmt);
}

auto Parser::parseContinueStmt() -> void {
  assert(at(SyntaxKind::KeywordContinue) &&
         "called parseContinueStmt without 'continue'");
  auto C = open();
  expect(SyntaxKind::KeywordContinue);
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::ContinueStmt);
}

auto Parser::parseReturnStmt() -> void {
  assert(at(SyntaxKind::KeywordReturn) &&
         "called parseReturnStmt without 'return'");
  auto C = open();
  expect(SyntaxKind::KeywordReturn);
  if (atExprStart())
    parseExpr();
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::ReturnStmt);
}

auto Parser::parseExprStmt() -> void {
  assert(atExprStart() && "called parseExprStmt without expr start");
  auto C = open();
  parseExpr();
  expect(SyntaxKind::Semicolon);
  close(C, SyntaxKind::ExprStmt);
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
    LHS = close(C, getUnaryExprSyntaxKind(Tok));
  } else {
    llvm_unreachable("LHS was meant to be guaranteed to be assigned here");
  }

  // We parse postfix operators in a loop until there are no more
  while (atPostfixOperator()) {
    auto C = insert(LHS);
    switch (get()) {
    case SyntaxKind::LeftBracket:
    case SyntaxKind::LeftParen: {
      // Take the type arguments if present
      if (eat(SyntaxKind::LeftBracket)) {
        auto CC = open();
        while (!eof() && !at(SyntaxKind::RightBracket)) {
          if (atTypeStart()) {
            parseType();
          } else {
            if (at(TSCallExpressionTypeArgumentListRecovery)) {
              break;
            }
            report<ExpectedCallExpressionTypeArgumentDiagnostic>(
                getTokenLength(), getSyntaxKindName(get()));
          }
          if (!at(SyntaxKind::RightParen)) {
            eat(SyntaxKind::Comma);
          }
        }
        expect(SyntaxKind::RightBracket);
        close(CC, SyntaxKind::CallExprTypeArgumentList);
      }
      // Next, we parse the required call arguments.
      auto CC = open();
      expect(SyntaxKind::LeftParen);
      while (!eof() && !at(SyntaxKind::RightParen)) {
        if (atExprStart()) {
          parseExpr();
        } else {
          if (at(TSCallExpressionArgumentListRecovery)) {
            break;
          }
          report<ExpectedCallExpressionArgumentDiagnostic>(
              getTokenLength(), getSyntaxKindName(get()));
        }
        if (!at(SyntaxKind::RightParen)) {
          eat(SyntaxKind::Comma);
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

  // At this point, we are guaranteed to have an LHS
  while (atInfixOperator() && Current <= getInfixPrecedence(get())) {
    // Finally, we consider if there is a infix expression to be built here.
    auto Tok = get();
    if (!atInfixOperator())
      return;
    auto C = insert(LHS);
    advance();
    auto NextPrecedence = getInfixPrecedence(Tok);
    if (atExprStart())
      parseExpr(NextPrecedence);
    LHS = close(C, getBinaryExprSyntaxKind(Tok));
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
  return close(C, SyntaxKind::IntegerLiteralExpr);
}

auto Parser::parseBooleanLiteralExpr() -> CloseCheckpoint {
  static const TokenSet TS =
      (1 << SyntaxKind::TrueLiteral) | (1 << SyntaxKind::FalseLiteral);
  assert(at(TS) && "called parseBooleanLiteral without 'true' or 'false'");
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
    auto CC = open();
    while (!eof() && !at(SyntaxKind::RightBrace)) {
      if (at(SyntaxKind::Identifier)) {
        parseConstructionExprMember();
      } else {
        if (at(TSCallExpressionArgumentListRecovery)) {
          break;
        }
        report<ExpectedConstructionExprMemberDiagnostic>(
            getTokenLength(), getSyntaxKindName(get()));
      }
    }
    expect(SyntaxKind::RightBrace);
    close(CC, SyntaxKind::ConstructionExprMemberList);
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
  switch (get()) {
  case SyntaxKind::Identifier:
    parseNamedType();
    break;
  case SyntaxKind::Star:
    parsePointerType();
    break;
  default:
    llvm_unreachable("unreachable");
  }
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
