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
    // Special kinds
  case SyntaxKind::Error:
    return "<error>";
  case SyntaxKind::Eof:
    return "<end of file>";

    // Syntax nodes
  case SyntaxKind::TranslationUnit:
    return "TranslationUnit";
  case SyntaxKind::Function:
    return "Function";
  case SyntaxKind::FunctionTypeParameterList:
    return "FunctionTypeParameterList";
  case SyntaxKind::FunctionTypeParameter:
    return "FunctionTypeParameter";
  case SyntaxKind::FunctionParameter:
    return "FunctionParameter";
  case SyntaxKind::FunctionParameterList:
    return "FunctionParameterList";
  case SyntaxKind::FunctionReturnType:
    return "FunctionReturnType";
  case SyntaxKind::FunctionBody:
    return "FunctionBody";

  case SyntaxKind::Stmt:
    return "Stmt";
  case SyntaxKind::LetStmt:
    return "LetStmt";

  case SyntaxKind::Expr:
    return "Expr";
  case SyntaxKind::IntegerLiteralExpr:
    return "IntegerLiteralExpr";
  case SyntaxKind::TrueLiteralExpr:
    return "TrueLiteralExpr";
  case SyntaxKind::FalseLiteralExpr:
    return "FalseLiteralExpr";
  case SyntaxKind::ReferenceExpr:
    return "ReferenceExpr";
  case SyntaxKind::GroupExpr:
    return "GroupExpr";
  case SyntaxKind::ConstantIndexExpr:
    return "ConstantIndexExpr";
  case SyntaxKind::CallExpr:
    return "CallExpr";
  case SyntaxKind::CallExprArgumentList:
    return "CallExprArgumentList";
  case SyntaxKind::UnaryExpr:
    return "UnaryExpr";
  case SyntaxKind::BinaryExpr:
    return "BinaryExpr";
  case SyntaxKind::ConstructionExpr:
    return "ConstructionExpr";
  case SyntaxKind::ConstructionExprMember:
    return "ConstructionExprMember";

  case SyntaxKind::Type:
    return "Type";
  case SyntaxKind::NamedType:
    return "NamedType";
  case SyntaxKind::PointerType:
    return "PointerType";

    // Syntax tokens
  case SyntaxKind::KeywordStruct:
    return "struct";
  case SyntaxKind::KeywordLet:
    return "let";
  case SyntaxKind::KeywordFn:
    return "fn";
  case SyntaxKind::KeywordIntrinsicFn:
    return "intrinsic_fn";
  case SyntaxKind::KeywordIntrinsicType:
    return "intrinsic_type";
  case SyntaxKind::KeywordTrait:
    return "trait";
  case SyntaxKind::KeywordInstance:
    return "instance";
  case SyntaxKind::KeywordIf:
    return "if";
  case SyntaxKind::KeywordElse:
    return "else";
  case SyntaxKind::KeywordReturn:
    return "return";
  case SyntaxKind::KeywordBreak:
    return "break";
  case SyntaxKind::KeywordContinue:
    return "continue";
  case SyntaxKind::KeywordFor:
    return "for";
  case SyntaxKind::KeywordNew:
    return "new";
  case SyntaxKind::Identifier:
    return "<identifier>";
  case SyntaxKind::IntegerLiteral:
    return "<integer literal>";
  case SyntaxKind::TrueLiteral:
    return "true";
  case SyntaxKind::FalseLiteral:
    return "false";
  case SyntaxKind::Comment:
    return "<comment>";
  case SyntaxKind::Whitespace:
    return "<whitespace>";
  case SyntaxKind::Newline:
    return "<newline>";
  case SyntaxKind::Ampersand:
    return "&";
  case SyntaxKind::Bang:
    return "!";
  case SyntaxKind::Plus:
    return "+";
  case SyntaxKind::Dot:
    return ".";
  case SyntaxKind::Star:
    return "*";
  case SyntaxKind::Minus:
    return "-";
  case SyntaxKind::Slash:
    return "/";
  case SyntaxKind::Equal:
    return "=";
  case SyntaxKind::EqualEqual:
    return "==";
  case SyntaxKind::BangEqual:
    return "!=";
  case SyntaxKind::Percent:
    return "%";
  case SyntaxKind::LeftParen:
    return "(";
  case SyntaxKind::LeftBracket:
    return "[";
  case SyntaxKind::LeftBrace:
    return "{";
  case SyntaxKind::LeftAngle:
    return "<";
  case SyntaxKind::LeftAngleEqual:
    return "<=";
  case SyntaxKind::RightParen:
    return ")";
  case SyntaxKind::RightBracket:
    return "]";
  case SyntaxKind::RightBrace:
    return "}";
  case SyntaxKind::RightAngle:
    return ">";
  case SyntaxKind::RightAngleEqual:
    return ">=";
  case SyntaxKind::Semicolon:
    return ";";
  case SyntaxKind::Colon:
    return ":";
  case SyntaxKind::ColonColon:
    return "::";
  case SyntaxKind::Comma:
    return ",";
  case SyntaxKind::Arrow:
    return "->";
  case SyntaxKind::AmpersandAmpersand:
    return "&&";
  case SyntaxKind::PipePipe:
    return "||";
  default:
    llvm_unreachable("Tried to recurse into unknown syntax kind");
  }
}

auto GreenNode::debug(raw_ostream &OS, size_t Indent) const -> void {
  // We don't quote this, because node is always a node kind
  OS << std::string(Indent, ' ') << "* " << getSyntaxKindName(getKind())
     << " len=" << getTextLength() << " children=" << Children.size() << "\n";
  for (const auto &Child : Children) {
    if (std::holds_alternative<GreenToken>(Child)) {
      auto &Token = std::get<GreenToken>(Child);
      OS << std::string(Indent + 2, ' ') << "| " << "Token '"
         << getSyntaxKindName(Token.getKind()) << "'"
         << " len=" << Token.getTextLength() << "\n";
    } else if (std::holds_alternative<std::shared_ptr<GreenNode>>(Child)) {
      auto &Node = std::get<std::shared_ptr<GreenNode>>(Child);
      Node->debug(OS, Indent + 2);
    } else {
      auto &ErrTok = std::get<ErrorToken>(Child);
      OS << std::string(Indent + 2, ' ') << "| " << "Error "
         << ErrTok.getDiagnosticID() << "\n";
    }
  }
}
