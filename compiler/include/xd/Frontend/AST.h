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

class ASTIntegerLiteralExpr : public ASTExpr {
public:
  explicit ASTIntegerLiteralExpr(std::shared_ptr<SyntaxNode> SN)
      : ASTExpr(SN) {}
  /// Get the integer value.
  auto getValue() const -> std::optional<llvm::APInt> {
    if (auto Lit = SN->findChild(SyntaxKind::IntegerLiteral); Lit.has_value()) {
      auto LitTok = llvm::dyn_cast<GreenToken>((*Lit)->getGreen().get());
      assert(LitTok != nullptr && "integer literal node was not a token");
      return llvm::APInt(32, LitTok->getText(), 10);
    }
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IntegerLiteralExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTIntegerLiteralExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::IntegerLiteralExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTIntegerLiteralExpr>(SN);
  }
};

class ASTBooleanLiteralExpr : public ASTExpr {
public:
  explicit ASTBooleanLiteralExpr(std::shared_ptr<SyntaxNode> SN)
      : ASTExpr(SN) {}
  /// Get the boolean value.
  auto getValue() const -> std::optional<bool> {
    if (auto Lit = SN->findChild(SyntaxKind::TrueLiteral); Lit.has_value())
      return true;
    if (auto Lit = SN->findChild(SyntaxKind::FalseLiteral); Lit.has_value())
      return false;
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::BooleanLiteralExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTBooleanLiteralExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::BooleanLiteralExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTBooleanLiteralExpr>(SN);
  }
};

class ASTCallExpr : public ASTExpr {
public:
  /// Member class representing the type argument list to the call expression.
  class TypeArgumentList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit TypeArgumentList(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the type argument list
    auto getTypeArguments() const
        -> std::optional<std::vector<std::shared_ptr<ASTType>>> {
      if (auto TypeArgs = SN->findChildren(isTypeSyntaxKind);
          TypeArgs.has_value()) {
        std::vector<std::shared_ptr<ASTType>> Result;
        for (auto TypeArg : *TypeArgs) {
          if (auto TA = ASTType::cast(TypeArg); TA.has_value())
            Result.push_back(*TA);
        }
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<TypeArgumentList>> {
      if (SN->getSyntaxKind() != SyntaxKind::CallExprTypeArgumentList ||
          !SN->isNode())
        return std::nullopt;
      return std::make_shared<TypeArgumentList>(SN);
    }
  };

  /// Member class representing the argument list to the call expression.
  class ArgumentList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ArgumentList(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the argument list.
    auto getArguments() const
        -> std::optional<std::vector<std::shared_ptr<ASTExpr>>> {
      if (auto Args = SN->findChildren(isExprSyntaxKind); Args.has_value()) {
        std::vector<std::shared_ptr<ASTExpr>> Result;
        for (auto Arg : *Args) {
          if (auto A = ASTExpr::cast(Arg); A.has_value())
            Result.push_back(*A);
        }
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<ArgumentList>> {
      if (SN->getSyntaxKind() != SyntaxKind::CallExprArgumentList ||
          !SN->isNode())
        return std::nullopt;
      return std::make_shared<ArgumentList>(SN);
    }
  };

  explicit ASTCallExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the expression that is being called
  auto getCallee() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Callee = SN->findChild(isExprSyntaxKind); Callee.has_value())
      return ASTExpr::cast(*Callee);
    return std::nullopt;
  }

  /// Get the type arguments provided to this call.
  auto getTypeArgumentList() const
      -> std::optional<std::shared_ptr<TypeArgumentList>> {
    if (auto TAL = SN->findChild(SyntaxKind::CallExprTypeArgumentList);
        TAL.has_value())
      return TypeArgumentList::cast(*TAL);
    return std::nullopt;
  }

  /// Get the arguments provided to this call.
  auto getArgumentList() const -> std::optional<std::shared_ptr<ArgumentList>> {
    if (auto AL = SN->findChild(SyntaxKind::CallExprArgumentList);
        AL.has_value())
      return ArgumentList::cast(*AL);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::CallExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTCallExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::CallExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTCallExpr>(SN);
  }
};

class ASTConstructionExpr : public ASTExpr {
public:
  /// Member class representing a single member. This is here because each
  /// member is a tuple of (name, value) and cannot be represented like an atom
  /// in the same way CallExpr arguments can.
  class ConstructionMember {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ConstructionMember(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the member name
    auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
      if (auto Name = SN->findChild(SyntaxKind::Identifier); Name.has_value())
        return Identifier::cast(*Name);
      return std::nullopt;
    }

    /// Get the value
    auto getValue() const -> std::optional<std::shared_ptr<ASTExpr>> {
      if (auto Value = SN->findChild(isExprSyntaxKind); Value.has_value())
        return ASTExpr::cast(*Value);
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<ConstructionMember>> {
      if (SN->getSyntaxKind() != SyntaxKind::ConstructionExprMember ||
          !SN->isNode())
        return std::nullopt;
      return std::make_shared<ConstructionMember>(SN);
    }
  };

  /// Member class representing the set of values being initialized into the
  /// struct.
  class ConstructionMemberList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ConstructionMemberList(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the members.
    auto getMembers() const
        -> std::optional<std::vector<std::shared_ptr<ConstructionMember>>> {
      if (auto Members = SN->findChildren(SyntaxKind::ConstructionExprMember);
          Members.has_value()) {
        std::vector<std::shared_ptr<ConstructionMember>> Result;
        for (auto Member : *Members) {
          if (auto M = ConstructionMember::cast(Member); M.has_value())
            Result.push_back(*M);
        }
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<ConstructionMemberList>> {
      if (SN->getSyntaxKind() != SyntaxKind::ConstructionExprMemberList ||
          !SN->isNode())
        return std::nullopt;
      return std::make_shared<ConstructionMemberList>(SN);
    }
  };

  explicit ASTConstructionExpr(std::shared_ptr<SyntaxNode> SN) : ASTExpr(SN) {}
  /// Get the construction initializer member list.
  auto getMemberList() const
      -> std::optional<std::shared_ptr<ConstructionMemberList>> {
    if (auto ML = SN->findChild(SyntaxKind::ConstructionExprMemberList);
        ML.has_value())
      return ConstructionMemberList::cast(*ML);
    return std::nullopt;
  }

  /// Get the type being constructed
  auto getConstructorType() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto CT = SN->findChild(isTypeSyntaxKind); CT.has_value())
      return ASTType::cast(*CT);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ConstructionExpr;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTConstructionExpr>> {
    if (SN->getSyntaxKind() != SyntaxKind::ConstructionExpr || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTConstructionExpr>(SN);
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

class ASTLetStmt : public ASTStmt {
public:
  explicit ASTLetStmt(std::shared_ptr<SyntaxNode> SN) : ASTStmt(SN) {}
  /// Get the name of the let binding.
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Name = SN->findChild(SyntaxKind::Identifier); Name.has_value())
      return Identifier::cast(*Name);
    return std::nullopt;
  }

  /// Get the optional type annotation of the let binding.
  auto getTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto T = SN->findChild(isTypeSyntaxKind); T.has_value())
      return ASTType::cast(*T);
    return std::nullopt;
  }

  /// Get the initializer of the let binding.
  auto getInitializerExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
      return ASTExpr::cast(*Expr);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::LetStmt;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTStmt>> {
    if (SN->getSyntaxKind() != SyntaxKind::LetStmt || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTStmt>(SN);
  }
};

class ASTIfStmt : public ASTStmt {
public:
  /// Member class for the true block.
  class ThenBody {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ThenBody(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the statement list
    auto getStmtList() const
        -> std::optional<std::vector<std::shared_ptr<ASTStmt>>> {
      if (auto SL = SN->findChildren(isStmtSyntaxKind); SL.has_value()) {
        std::vector<std::shared_ptr<ASTStmt>> Result;
        for (auto Stmt : *SL)
          if (auto S = ASTStmt::cast(Stmt); S.has_value())
            Result.push_back(*S);
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<ThenBody>> {
      if (SN->getSyntaxKind() != SyntaxKind::IfThenBody || !SN->isNode())
        return std::nullopt;
      return std::make_shared<ThenBody>(SN);
    }
  };

  /// Member class for the false block.
  class ElseBody {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ElseBody(std::shared_ptr<SyntaxNode> SN) : SN(SN) {}
    /// Get the statement list.
    auto getStmtList() const
        -> std::optional<std::vector<std::shared_ptr<ASTStmt>>> {
      if (auto SL = SN->findChildren(isStmtSyntaxKind); SL.has_value()) {
        std::vector<std::shared_ptr<ASTStmt>> Result;
        for (auto Stmt : *SL)
          if (auto S = ASTStmt::cast(Stmt); S.has_value())
            Result.push_back(*S);
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(std::shared_ptr<SyntaxNode> SN)
        -> std::optional<std::shared_ptr<ElseBody>> {
      if (SN->getSyntaxKind() != SyntaxKind::IfElseBody || !SN->isNode())
        return std::nullopt;
      return std::make_shared<ElseBody>(SN);
    }
  };

  explicit ASTIfStmt(std::shared_ptr<SyntaxNode> SN) : ASTStmt(SN) {}
  /// Get the condition of the if statement
  auto getConditionExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
      return ASTExpr::cast(*Expr);
    return std::nullopt;
  }

  /// Get the body that executes if the condition is true.
  auto getThenBody() const -> std::optional<std::shared_ptr<ThenBody>> {
    if (auto TB = SN->findChild(SyntaxKind::IfThenBody); TB.has_value())
      return ThenBody::cast(*TB);
    return std::nullopt;
  }

  /// Get the body that executes if the condition is false.
  auto getElseBody() const -> std::optional<std::shared_ptr<ElseBody>> {
    if (auto EB = SN->findChild(SyntaxKind::IfElseBody); EB.has_value())
      return ElseBody::cast(*EB);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IfStmt;
  }
  static auto cast(std::shared_ptr<SyntaxNode> SN)
      -> std::optional<std::shared_ptr<ASTIfStmt>> {
    if (SN->getSyntaxKind() != SyntaxKind::IfStmt || !SN->isNode())
      return std::nullopt;
    return std::make_shared<ASTIfStmt>(SN);
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
