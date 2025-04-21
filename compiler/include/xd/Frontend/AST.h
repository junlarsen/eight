//===----- AST.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_AST_H
#define XD_FRONTEND_AST_H

#include "xd/Basic/Location.h"
#include "xd/Frontend/Syntax.h"
#include "llvm/Support/Casting.h"

namespace xd {
class ASTDecl;
class ASTFunctionDecl;
class ASTTypeDecl;
class ASTStructDecl;
class ASTTraitDecl;
class ASTInstanceDecl;

class ASTStmt;
class ASTLetStmt;
class ASTReturnStmt;
class ASTForStmt;
class ASTBreakStmt;
class ASTContinueStmt;
class ASTIfStmt;
class ASTExprStmt;

class ASTExpr;
class ASTIntegerLiteralExpr;
class ASTBooleanLiteralExpr;
class ASTAssignmentExpr;
class ASTBinaryOperatorExpr;
class ASTUnaryOperatorExpr;
class ASTConstantIndexExpr;
class ASTVariableIndexExpr;
class ASTReferenceExpr;
class ASTCallExpr;
class ASTConstructionExpr;
class ASTGroupingExpr;

class ASTType;
class ASTPointerType;
class ASTNamedType;

/// An identifier name.
///
/// This is not modelled as a part of the AST hierarchy because identifiers are
/// just names, not full-blown nodes.
class Identifier final {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit Identifier(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
  auto getLocation() const -> SourceLocation { return SN->getLocation(); }
  auto getName() const -> llvm::StringRef {
    return llvm::cast<GreenToken>(SN->getGreen().get())->getText();
  }

  /// Can the given SyntaxNode be cast to an Identifier?
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<Identifier>> {
    if (!SN->isToken() || SN->getSyntaxKind() != SyntaxKind::Identifier)
      return std::nullopt;
    return std::make_shared<Identifier>(SN);
  }
};

/// Any node in the abstract syntax tree.
///
/// This class does not have a `cast` method, because every node should be more
/// specific than ASTNode. It is very non-descriptive on its own by design.
class ASTNode {
protected:
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit ASTNode(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}

  auto getSyntaxKind() const -> SyntaxKind { return SN->getSyntaxKind(); }
  auto getLocation() const -> SourceLocation { return SN->getLocation(); }
  static bool classof(const ASTNode *Node) {
    return isNodeSyntaxKind(Node->getSyntaxKind());
  }
};

/// Any type node in the abstract syntax tree.
class ASTType : public ASTNode {
public:
  explicit ASTType(std::shared_ptr<SyntaxNode> SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isTypeSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTType>> {
    if (!isTypeSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTType>(SN);
  }
};

/// Represent a pointer type.
class ASTPointerType final : public ASTType {
public:
  explicit ASTPointerType(std::shared_ptr<SyntaxNode> SN) : ASTType(SN) {}

  /// Get the type that this type is a pointer to.
  auto getInnerType() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto Inner = SN->findChild(isTypeSyntaxKind); Inner.has_value())
      return ASTType::cast(*Inner);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::PointerType;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTPointerType>> {
    if (SN->getSyntaxKind() != SyntaxKind::PointerType || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTPointerType>(SN);
  }
};

/// Represent a named type such as `int`.
class ASTNamedType final : public ASTType {
public:
  explicit ASTNamedType(std::shared_ptr<SyntaxNode> SN) : ASTType(SN) {}

  /// Get the name of the type.
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::NamedType;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTNamedType>> {
    if (SN->getSyntaxKind() != SyntaxKind::NamedType || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTNamedType>(SN);
  }
};

class ASTExpr : public ASTNode {
public:
  explicit ASTExpr(std::shared_ptr<SyntaxNode> SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isExprSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTExpr>> {
    if (!isExprSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTExpr>(SN);
  }
};

class ASTStmt : public ASTNode {
public:
  explicit ASTStmt(std::shared_ptr<SyntaxNode> SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isStmtSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTStmt>> {
    if (!isStmtSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTStmt>(SN);
  }
};

class ASTDecl : public ASTNode {
public:
  explicit ASTDecl(std::shared_ptr<SyntaxNode> SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isDeclSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTDecl>> {
    if (!isDeclSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTDecl>(SN);
  }
};
} // namespace xd

#endif // XD_FRONTEND_AST_H
