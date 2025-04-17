//===----- Syntax.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Syntax.h"
#include "llvm/Support/ErrorHandling.h"

using namespace llvm;
using namespace xd;

auto xd::getSyntaxKindName(SyntaxKind SK) -> StringRef {
  switch (SK) {
  case SyntaxKind::Identifier:
    return "Identifier";
  case SyntaxKind::IntegerLiteral:
    return "IntegerLiteral";
  case SyntaxKind::Error:
    return "Error";
  case SyntaxKind::Eof:
    return "Eof";
  case SyntaxKind::TranslationUnit:
    return "TranslationUnit";
  case SyntaxKind::Function:
    return "Function";
  case SyntaxKind::FunctionParameterList:
    return "FunctionParameterList";
  case SyntaxKind::FunctionBody:
    return "FunctionBody";
  case SyntaxKind::KeywordStruct:
    return "KeywordStruct";
  case SyntaxKind::KeywordLet:
    return "KeywordLet";
  case SyntaxKind::KeywordFn:
    return "KeywordFn";
  case SyntaxKind::KeywordIntrinsicFn:
    return "KeywordIntrinsicFn";
  case SyntaxKind::KeywordIntrinsicType:
    return "KeywordIntrinsicType";
  case SyntaxKind::KeywordTrait:
    return "KeywordTrait";
  case SyntaxKind::KeywordInstance:
    return "KeywordInstance";
  case SyntaxKind::KeywordIf:
    return "KeywordIf";
  case SyntaxKind::KeywordElse:
    return "KeywordElse";
  case SyntaxKind::KeywordReturn:
    return "KeywordReturn";
  case SyntaxKind::KeywordBreak:
    return "KeywordBreak";
  case SyntaxKind::KeywordContinue:
    return "KeywordContinue";
  case SyntaxKind::KeywordFor:
    return "KeywordFor";
  case SyntaxKind::KeywordNew:
    return "KeywordNew";
  case SyntaxKind::TrueLiteral:
    return "TrueLiteral";
  case SyntaxKind::FalseLiteral:
    return "FalseLiteral";
  case SyntaxKind::Comment:
    return "Comment";
  case SyntaxKind::Whitespace:
    return "Whitespace";
  case SyntaxKind::Newline:
    return "Newline";
  case SyntaxKind::Ampersand:
    return "Ampersand";
  case SyntaxKind::Bang:
    return "Bang";
  case SyntaxKind::Plus:
    return "Plus";
  case SyntaxKind::Dot:
    return "Dot";
  case SyntaxKind::Star:
    return "Star";
  case SyntaxKind::Minus:
    return "Minus";
  case SyntaxKind::Slash:
    return "Slash";
  case SyntaxKind::Equal:
    return "Equal";
  case SyntaxKind::EqualEqual:
    return "EqualEqual";
  case SyntaxKind::BangEqual:
    return "BangEqual";
  case SyntaxKind::Percent:
    return "Percent";
  case SyntaxKind::LeftParen:
    return "LeftParen";
  case SyntaxKind::LeftBracket:
    return "LeftBracket";
  case SyntaxKind::LeftBrace:
    return "LeftBrace";
  case SyntaxKind::LeftAngle:
    return "LeftAngle";
  case SyntaxKind::LeftAngleEqual:
    return "LeftAngleEqual";
  case SyntaxKind::RightParen:
    return "RightParen";
  case SyntaxKind::RightBracket:
    return "RightBracket";
  case SyntaxKind::RightBrace:
    return "RightBrace";
  case SyntaxKind::RightAngle:
    return "RightAngle";
  case SyntaxKind::RightAngleEqual:
    return "RightAngleEqual";
  case SyntaxKind::Semicolon:
    return "Semicolon";
  case SyntaxKind::Colon:
    return "Colon";
  case SyntaxKind::ColonColon:
    return "ColonColon";
  case SyntaxKind::Comma:
    return "Comma";
  case SyntaxKind::Arrow:
    return "Arrow";
  case SyntaxKind::AmpersandAmpersand:
    return "AmpersandAmpersand";
  case SyntaxKind::PipePipe:
    return "PipePipe";
  default:
    llvm_unreachable("Tried to recurse into unknown syntax kind");
  }
}

auto GreenNode::debug(raw_ostream &OS, size_t Indent) const -> void {
  OS << std::string(Indent, ' ') << getSyntaxKindName(getKind())
     << " len=" << getTextLength() << " children=" << Children.size() << "\n";
  for (const auto &Child : Children) {
    if (std::holds_alternative<GreenToken>(Child)) {
      auto &Token = std::get<GreenToken>(Child);
      OS << std::string(Indent + 2, ' ') << getSyntaxKindName(Token.getKind())
         << " len=" << Token.getTextLength() << "\n";
    } else {
      auto &Node = std::get<std::shared_ptr<GreenNode>>(Child);
      Node->debug(OS, Indent + 2);
    }
  }
}
