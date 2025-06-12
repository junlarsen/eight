//===----- Syntax.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Syntax.h"
#include "llvm/Support/Casting.h"
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
  case SyntaxKind::Decl:
    return "Decl";
  case SyntaxKind::ImportDecl:
    return "ImportDecl";
  case SyntaxKind::ModuleDecl:
    return "ModuleDecl";
  case SyntaxKind::IntrinsicFunctionDecl:
    return "IntrinsicFunctionDecl";
  case SyntaxKind::FunctionDecl:
    return "FunctionDecl";
  case SyntaxKind::FunctionTypeParameterList:
    return "FunctionTypeParameterList";
  case SyntaxKind::FunctionTypeParameter:
    return "FunctionTypeParameter";
  case SyntaxKind::FunctionParameter:
    return "FunctionParameter";
  case SyntaxKind::FunctionParameterList:
    return "FunctionParameterList";
  case SyntaxKind::FunctionBody:
    return "FunctionBody";
  case SyntaxKind::IntrinsicTypeDecl:
    return "IntrinsicTypeDecl";
  case SyntaxKind::StructDecl:
    return "StructDecl";
  case SyntaxKind::StructMemberList:
    return "StructMemberList";
  case SyntaxKind::StructMember:
    return "StructMember";
  case SyntaxKind::TraitDecl:
    return "TraitDecl";
  case SyntaxKind::TraitTypeParameterList:
    return "TraitTypeParameterList";
  case SyntaxKind::TraitTypeParameter:
    return "TraitTypeParameter";
  case SyntaxKind::TraitMemberList:
    return "TraitMemberList";
  case SyntaxKind::TraitFunctionMember:
    return "TraitIntrinsicFunctionMember";
  case SyntaxKind::InstanceDecl:
    return "InstanceDecl";
  case SyntaxKind::InstanceTypeArgumentList:
    return "InstanceTypeArgumentList";
  case SyntaxKind::InstanceMemberList:
    return "InstanceMemberList";

  case SyntaxKind::Stmt:
    return "Stmt";
  case SyntaxKind::LetStmt:
    return "LetStmt";
  case SyntaxKind::IfStmt:
    return "IfStmt";
  case SyntaxKind::IfThenBody:
    return "IfThenBody";
  case SyntaxKind::IfElseBody:
    return "IfElseBody";
  case SyntaxKind::ForStmt:
    return "ForStmt";
  case SyntaxKind::ForInitializer:
    return "ForInitializer";
  case SyntaxKind::ForCondition:
    return "ForCondition";
  case SyntaxKind::ForIncrement:
    return "ForIncrement";
  case SyntaxKind::ForBody:
    return "ForBody";
  case SyntaxKind::ReturnStmt:
    return "ReturnStmt";
  case SyntaxKind::ContinueStmt:
    return "ContinueStmt";
  case SyntaxKind::BreakStmt:
    return "BreakStmt";
  case SyntaxKind::ExprStmt:
    return "ExprStmt";

  case SyntaxKind::Expr:
    return "Expr";
  case SyntaxKind::IntegerLiteralExpr:
    return "IntegerLiteralExpr";
  case SyntaxKind::BooleanLiteralExpr:
    return "BooleanLiteralExpr";
  case SyntaxKind::StringLiteralExpr:
    return "StringLiteralExpr";
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
  case SyntaxKind::CallExprTypeArgumentList:
    return "CallExprTypeArgumentList";
  case SyntaxKind::UnaryNotExpr:
    return "UnaryNotExpr";
  case SyntaxKind::UnaryMinusExpr:
    return "UnaryMinusExpr";
  case SyntaxKind::UnaryPlusExpr:
    return "UnaryPlusExpr";
  case SyntaxKind::UnaryDerefExpr:
    return "UnaryDerefExpr";
  case SyntaxKind::UnaryAddrOfExpr:
    return "UnaryAddrOfExpr";
  case SyntaxKind::BinaryLogicalAndExpr:
    return "BinaryLogicalAndExpr";
  case SyntaxKind::BinaryLogicalOrExpr:
    return "BinaryLogicalOrExpr";
  case SyntaxKind::BinaryAssignExpr:
    return "BinaryAssignExpr";
  case SyntaxKind::BinaryEqualityExpr:
    return "BinaryEqualityExpr";
  case SyntaxKind::BinaryInequalityExpr:
    return "BinaryInequalityExpr";
  case SyntaxKind::BinaryLessThanExpr:
    return "BinaryLessThanExpr";
  case SyntaxKind::BinaryGreaterThanExpr:
    return "BinaryGreaterThanExpr";
  case SyntaxKind::BinaryGreaterThanEqualExpr:
    return "BinaryGreaterThanEqualExpr";
  case SyntaxKind::BinaryLessThanEqualExpr:
    return "BinaryLessThanEqualExpr";
  case SyntaxKind::BinaryAddExpr:
    return "BinaryAddExpr";
  case SyntaxKind::BinarySubExpr:
    return "BinarySubExpr";
  case SyntaxKind::BinaryMulExpr:
    return "BinaryMulExpr";
  case SyntaxKind::BinaryDivExpr:
    return "BinaryDivExpr";
  case SyntaxKind::BinaryModulusExpr:
    return "BinaryModulusExpr";
  case SyntaxKind::ConstructionExpr:
    return "ConstructionExpr";
  case SyntaxKind::ConstructionExprMemberList:
    return "ConstructionExprMemberList";
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
  case SyntaxKind::KeywordImport:
    return "import";
  case SyntaxKind::KeywordFrom:
    return "from";
  case SyntaxKind::Identifier:
    return "<identifier>";
  case SyntaxKind::IntegerLiteral:
    return "<integer literal>";
  case SyntaxKind::TrueLiteral:
    return "true";
  case SyntaxKind::FalseLiteral:
    return "false";
  case SyntaxKind::StringLiteral:
    return "<string literal>";
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
  OS << std::string(Indent, ' ') << "* " << getSyntaxKindName(getSyntaxKind())
     << " len=" << getTextLength() << " children=" << Children.size() << "\n";
  for (auto &Child : Children) {
    if (const auto *GT = dyn_cast<GreenToken>(Child.get())) {
      OS << std::string(Indent + 2, ' ') << "| " << "Token '"
         << getSyntaxKindName(GT->getSyntaxKind()) << "'"
         << " len=" << GT->getTextLength() << "\n";
    } else if (const auto *GE = dyn_cast<GreenError>(Child.get())) {
      OS << std::string(Indent + 2, ' ') << "| " << "Error "
         << GE->getDiagnosticID() << "\n";
    } else if (auto *GN = dyn_cast<GreenNode>(Child.get())) {
      GN->debug(OS, Indent + 2);
    } else {
      llvm_unreachable("GreenNode is not a valid variant kind");
    }
  }
}

auto SyntaxNode::getLocation() const -> SourceLocation {
  return SourceLocation(Offset, Offset + getTextLength(), FileID);
}

auto SyntaxNode::debug(raw_ostream &OS, size_t Indent) const -> void {
  OS << std::string(Indent, ' ') << "SyntaxNode '"
     << getSyntaxKindName(Green->getSyntaxKind()) << "' (" << Children.size()
     << ") " << getLocation().getStart() << ".." << getLocation().getEnd()
     << "\n";
  for (auto &Child : Children) {
    Child->debug(OS, Indent + 2);
  }
}

auto SyntaxNode::findChildAtIndex(SyntaxKind SK, size_t Index) const
    -> std::optional<std::shared_ptr<SyntaxNode>> {
  size_t I = 0;
  for (auto &Child : Children) {
    if (Child->getSyntaxKind() == SK) {
      if (I == Index)
        return Child;
      I++;
    }
  }
  return std::nullopt;
}

auto SyntaxNode::findChildAtIndex(
    const std::function<bool(SyntaxKind)> &Predicate, size_t Index) const
    -> std::optional<std::shared_ptr<SyntaxNode>> {
  size_t I = 0;
  for (auto &Child : Children) {
    if (Predicate(Child->getSyntaxKind())) {
      if (I == Index)
        return Child;
      I++;
    }
  }
  return std::nullopt;
}

auto SyntaxNode::findChildren(SyntaxKind SK) const
    -> std::optional<std::vector<std::shared_ptr<SyntaxNode>>> {
  if (Children.empty())
    return std::nullopt;

  std::vector<std::shared_ptr<SyntaxNode>> Matches;
  for (auto &Child : Children) {
    if (Child->getSyntaxKind() == SK)
      Matches.push_back(Child);
  }
  return Matches;
}

auto SyntaxNode::findChildren(const std::function<bool(SyntaxKind)> &Predicate)
    const -> std::optional<std::vector<std::shared_ptr<SyntaxNode>>> {
  if (Children.empty())
    return std::nullopt;

  std::vector<std::shared_ptr<SyntaxNode>> Matches;
  for (auto &Child : Children) {
    if (Predicate(Child->getSyntaxKind()))
      Matches.push_back(Child);
  }
  return Matches;
}

auto SyntaxNode::findSibling(SyntaxKind SK) const
    -> std::optional<std::shared_ptr<SyntaxNode>> {
  auto P = getParent();
  if (P == std::nullopt)
    return std::nullopt;
  return P->get()->findChild(SK);
}

auto SyntaxNode::findSibling(const std::function<bool(SyntaxKind)> &Predicate)
    const -> std::optional<std::shared_ptr<SyntaxNode>> {
  auto P = getParent();
  if (P == std::nullopt)
    return std::nullopt;
  return P->get()->findChild(Predicate);
}

static auto buildChildTree(const std::shared_ptr<SyntaxNode> &Parent,
                           uint32_t Index, uint32_t Offset,
                           std::shared_ptr<GreenElement> Elem,
                           DiagnosticManager &DM, SourceFileID FileID)
    -> std::shared_ptr<SyntaxNode> {
  auto Self = SyntaxNode::get(Parent, Elem, Offset, Index, FileID);

  // If this is an error node, then we can propagate the location to the diag
  // itself.
  if (auto *GE = dyn_cast<GreenError>(Elem.get())) {
    DM.addLocation(GE->getDiagnosticID(), Self->getLocation());
  }

  if (auto *GN = dyn_cast<GreenNode>(Elem.get())) {
    auto NextOffset = Offset;
    for (uint32_t I = 0; auto &C : GN->getChildren()) {
      auto Child = buildChildTree(Self, I, NextOffset, C, DM, FileID);
      // Do not duplicate offsets for errors
      if (!isa<GreenError>(Child->getGreen().get()))
        NextOffset += Child->getTextLength();
      I++;
    }
  }
  return Self;
}

auto xd::buildSyntaxTree(const std::shared_ptr<GreenNode> &GreenRoot,
                         DiagnosticManager &DM, SourceFileID FileID)
    -> std::shared_ptr<SyntaxNode> {
  auto Root = SyntaxNode::getRoot(GreenRoot, FileID);
  auto Offset = 0;
  for (uint32_t I = 0; auto &C : GreenRoot->getChildren()) {
    auto Child = buildChildTree(Root, I, Offset, C, DM, FileID);
    // Do not duplicate offsets for errors
    if (!isa<GreenError>(Child->getGreen().get()))
      Offset += Child->getTextLength();
    I++;
  }
  return Root;
}
