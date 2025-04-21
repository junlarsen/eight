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
#include "llvm/Support/ErrorHandling.h"

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
class ASTBinaryOperatorExpr;
class ASTUnaryOperatorExpr;
class ASTConstantIndexExpr;
class ASTReferenceExpr;
class ASTCallExpr;
class ASTConstructionExpr;
class ASTGroupExpr;

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

enum class ASTUnaryOperator {
  Not,
  Minus,
  Plus,
  Deref,
  AddrOf,
};

inline auto getUnaryOperator(SyntaxKind SK) -> ASTUnaryOperator {
  switch (SK) {
  case SyntaxKind::UnaryNotExpr:
    return ASTUnaryOperator::Not;
  case SyntaxKind::UnaryMinusExpr:
    return ASTUnaryOperator::Minus;
  case SyntaxKind::UnaryPlusExpr:
    return ASTUnaryOperator::Plus;
  case SyntaxKind::UnaryDerefExpr:
    return ASTUnaryOperator::Deref;
  case SyntaxKind::UnaryAddrOfExpr:
    return ASTUnaryOperator::AddrOf;
  default:
    llvm_unreachable("invalid unary operator");
  }
}

/// Represent a unary operation.
class ASTUnaryExpr : public ASTExpr {
public:
  explicit ASTUnaryExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the operator kind.
  ///
  /// This does not return an optional node, because the UnaryExpr in the AST
  /// represents all possible UnaryExpr syntax kinds in the red tree.
  auto getOperator() const -> ASTUnaryOperator {
    return getUnaryOperator(SN->getSyntaxKind());
  }

  /// Get the left-hand side operand.
  auto getOperand() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Operand = SN->findChild(isExprSyntaxKind); Operand.has_value())
      return ASTExpr::cast(*Operand);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return isUnaryExprSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTUnaryExpr>> {
    if (!isUnaryExprSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTUnaryExpr>(SN);
  }
};

enum class ASTBinaryOperator {
  LogicalAnd,
  LogicalOr,
  Assign,
  Equality,
  Inequality,
  LessThan,
  GreaterThan,
  LessThanEqual,
  GreaterThanEqual,
  Add,
  Sub,
  Mul,
  Div,
  Modulus,
};

inline auto getBinaryOperator(SyntaxKind SK) -> ASTBinaryOperator {
  switch (SK) {
  case SyntaxKind::BinaryLogicalAndExpr:
    return ASTBinaryOperator::LogicalAnd;
  case SyntaxKind::BinaryLogicalOrExpr:
    return ASTBinaryOperator::LogicalOr;
  case SyntaxKind::BinaryAssignExpr:
    return ASTBinaryOperator::Assign;
  case SyntaxKind::BinaryEqualityExpr:
    return ASTBinaryOperator::Equality;
  case SyntaxKind::BinaryInequalityExpr:
    return ASTBinaryOperator::Inequality;
  case SyntaxKind::BinaryLessThanExpr:
    return ASTBinaryOperator::LessThan;
  case SyntaxKind::BinaryGreaterThanExpr:
    return ASTBinaryOperator::GreaterThan;
  case SyntaxKind::BinaryLessThanEqualExpr:
    return ASTBinaryOperator::LessThanEqual;
  case SyntaxKind::BinaryGreaterThanEqualExpr:
    return ASTBinaryOperator::GreaterThanEqual;
  case SyntaxKind::BinaryAddExpr:
    return ASTBinaryOperator::Add;
  case SyntaxKind::BinarySubExpr:
    return ASTBinaryOperator::Sub;
  case SyntaxKind::BinaryMulExpr:
    return ASTBinaryOperator::Mul;
  case SyntaxKind::BinaryDivExpr:
    return ASTBinaryOperator::Div;
  case SyntaxKind::BinaryModulusExpr:
    return ASTBinaryOperator::Modulus;
  default:
    llvm_unreachable("invalid binary operator");
  }
}

class ASTBinaryExpr : public ASTExpr {
public:
  explicit ASTBinaryExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the operator kind.
  ///
  /// This does not return an optional node, because the BinaryExpr in the AST
  /// represents all possible BinaryExpr syntax kinds in the red tree.
  auto getOperator() const -> ASTBinaryOperator {
    return getBinaryOperator(SN->getSyntaxKind());
  }

  /// Get the left-hand side of the operation.
  ///
  /// This is fixed as thr 1st Expr syntax kind node child.
  auto getLHS() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto LHS = SN->findChildAtIndex(isExprSyntaxKind, 0); LHS.has_value())
      return ASTExpr::cast(*LHS);
    return std::nullopt;
  }

  /// Get the right-hand side of the operation.
  ///
  /// This is fixed as the 2nd Expr syntax kind node child.
  auto getRHS() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto RHS = SN->findChildAtIndex(isExprSyntaxKind, 1); RHS.has_value())
      return ASTExpr::cast(*RHS);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return isBinaryExprSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTBinaryExpr>> {
    if (!isBinaryExprSyntaxKind(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTBinaryExpr>(SN);
  }
};

class ASTGroupExpr : public ASTExpr {
public:
  explicit ASTGroupExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  auto getInnerExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto InnerExpr = SN->findChildAtIndex(isExprSyntaxKind, 0);
        InnerExpr.has_value())
      return ASTExpr::cast(*InnerExpr);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::GroupExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTGroupExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::GroupExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTGroupExpr>(SN);
  }
};

class ASTConstantIndexExpr : public ASTExpr {
public:
  explicit ASTConstantIndexExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the expression the indexing is being done on.
  auto getOrigin() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Origin = SN->findChildAtIndex(isExprSyntaxKind, 0);
        Origin.has_value())
      return ASTExpr::cast(*Origin);
    return std::nullopt;
  }

  /// Get the named index that this expression is indexing.
  auto getIndex() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ConstantIndexExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTConstantIndexExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::ConstantIndexExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTConstantIndexExpr>(SN);
  }
};

class ASTReferenceExpr : public ASTExpr {
public:
  explicit ASTReferenceExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the variable name for this reference expression.
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Name = SN->findChild(SyntaxKind::Identifier); Name.has_value())
      return Identifier::cast(*Name);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ReferenceExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTReferenceExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::ReferenceExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTReferenceExpr>(SN);
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
