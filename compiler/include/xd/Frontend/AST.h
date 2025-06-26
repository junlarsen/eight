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
#include "xd/Basic/SourceManager.h"
#include "xd/Frontend/Syntax.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"

namespace xd {
class ASTModuleDecl;
class ASTDecl;
class ASTPackageDecl;
class ASTImportDecl;
class ASTFunctionDecl;
class ASTIntrinsicTypeDecl;
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
class ASTBinaryExpr;
class ASTUnaryExpr;
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
  explicit Identifier(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  auto getLocation() const -> SourceLocation { return SN->getLocation(); }
  auto getName() const -> llvm::StringRef {
    return llvm::cast<GreenToken>(SN->getGreen().get())->getText();
  }

  /// Can the given SyntaxNode be cast to an Identifier?
  static auto cast(const std::shared_ptr<SyntaxNode> &SN)
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
  explicit ASTNode(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}

  auto getSyntaxKind() const -> SyntaxKind { return SN->getSyntaxKind(); }
  auto getLocation() const -> SourceLocation { return SN->getLocation(); }
  static bool classof(const ASTNode *Node) {
    return isNodeSyntaxKind(Node->getSyntaxKind());
  }

  template <class T>
  static auto from(const std::shared_ptr<SyntaxNode> &SN,
                   const std::function<bool(SyntaxKind)> &Predicate)
      -> std::optional<std::shared_ptr<T>> {
    if (!Predicate(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<T>(SN);
  }

  template <class T>
  static auto from(const std::shared_ptr<SyntaxNode> &SN, SyntaxKind SK)
      -> std::optional<std::shared_ptr<T>> {
    return from<T>(SN, [&](SyntaxKind M) { return M == SK; });
  }

  template <class T>
  auto findSingle(const std::function<bool(SyntaxKind)> &Predicate) const
      -> std::optional<std::shared_ptr<T>> {
    if (auto It = SN->findChild(Predicate); It)
      return std::make_shared<T>(*It);
    return std::nullopt;
  }

  template <class T>
  auto findSingle(SyntaxKind SK) const -> std::optional<std::shared_ptr<T>> {
    return findSingle<T>([&](SyntaxKind M) { return M == SK; });
  }

  template <class T>
  auto findMany(const std::function<bool(SyntaxKind)> &Predicate) const
      -> std::optional<std::vector<std::shared_ptr<T>>> {
    if (auto IT = SN->findChildren(Predicate); IT) {
      std::vector<std::shared_ptr<T>> Result;
      for (auto I : *IT)
        if (auto Cast = T::cast(I); Cast)
          Result.push_back(*Cast);
      return Result;
    }
    return std::nullopt;
  }

  template <class T>
  auto findMany(SyntaxKind SK) const
      -> std::optional<std::vector<std::shared_ptr<T>>> {
    return findMany<T>([&](SyntaxKind M) { return M == SK; });
  }
};

/// Any type node in the abstract syntax tree.
class ASTType : public ASTNode {
public:
  explicit ASTType(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isTypeSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTType>(SN, isTypeSyntaxKind);
  }
};

/// Represent a pointer type.
class ASTPointerType final : public ASTType {
public:
  explicit ASTPointerType(const std::shared_ptr<SyntaxNode> &SN)
      : ASTType(SN) {}

  /// Get the type that this type is a pointer to.
  auto getInnerType() const { return findSingle<ASTType>(isTypeSyntaxKind); }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::PointerType;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTPointerType>(SN, SyntaxKind::PointerType);
  }
};

/// Represent a named type such as `int`.
class ASTNamedType final : public ASTType {
public:
  explicit ASTNamedType(const std::shared_ptr<SyntaxNode> &SN) : ASTType(SN) {}

  /// Get the name of the type.
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::NamedType;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTNamedType>(SN, SyntaxKind::NamedType);
  }
};

class ASTExpr : public ASTNode {
public:
  explicit ASTExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isExprSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTExpr>(SN, isExprSyntaxKind);
  }
};

/// Member class representing the type argument list to the call expression.
template <SyntaxKind ListKind>
class ASTTypeArgumentListFragment : public ASTNode {
public:
  explicit ASTTypeArgumentListFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the type argument list
  auto getTypeArguments() const { return findMany<ASTType>(isTypeSyntaxKind); }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTTypeArgumentListFragment>(SN, ListKind);
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
  explicit ASTUnaryExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTExpr(SN) {}
  /// Get the operator kind.
  ///
  /// This does not return an optional node, because the UnaryExpr in the AST
  /// represents all possible UnaryExpr syntax kinds in the red tree.
  auto getOperator() const -> ASTUnaryOperator {
    return getUnaryOperator(SN->getSyntaxKind());
  }

  /// Get the left-hand side operand.
  auto getOperand() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  static bool classof(const ASTNode *Node) {
    return isUnaryExprSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTUnaryExpr>(SN, isUnaryExprSyntaxKind);
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
  explicit ASTBinaryExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTExpr(SN) {}
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
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTBinaryExpr>(SN, isBinaryExprSyntaxKind);
  }
};

class ASTGroupExpr : public ASTExpr {
public:
  explicit ASTGroupExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTExpr(SN) {}
  auto getInnerExpr() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::GroupExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTGroupExpr>(SN, SyntaxKind::GroupExpr);
  }
};

class ASTConstantIndexExpr : public ASTExpr {
public:
  explicit ASTConstantIndexExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
  /// Get the expression the indexing is being done on.
  auto getOrigin() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  /// Get the named index that this expression is indexing.
  auto getIndex() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ConstantIndexExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTConstantIndexExpr>(SN, SyntaxKind::ConstantIndexExpr);
  }
};

class ASTReferenceExpr : public ASTExpr {
public:
  explicit ASTReferenceExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
  /// Get the variable name for this reference expression.
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ReferenceExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTReferenceExpr>(SN, SyntaxKind::ReferenceExpr);
  }
};

class ASTIntegerLiteralExpr : public ASTExpr {
public:
  explicit ASTIntegerLiteralExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
  /// Get the integer value.
  auto getValue() const -> std::optional<llvm::APInt> {
    if (auto Lit = SN->findChild(SyntaxKind::IntegerLiteral); Lit.has_value()) {
      auto *LitTok = llvm::dyn_cast<GreenToken>((*Lit)->getGreen().get());
      assert(LitTok != nullptr && "integer literal node was not a token");
      // TODO: Assume bit size based on potential type suffix.
      return llvm::APInt(64, LitTok->getText(), 10);
    }
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IntegerLiteralExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTIntegerLiteralExpr>(SN, SyntaxKind::IntegerLiteralExpr);
  }
};

class ASTBooleanLiteralExpr : public ASTExpr {
public:
  explicit ASTBooleanLiteralExpr(const std::shared_ptr<SyntaxNode> &SN)
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
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTBooleanLiteralExpr>(SN, SyntaxKind::BooleanLiteralExpr);
  }
};

class ASTCallExpr : public ASTExpr {
public:
  /// Member class representing the argument list to the call expression.
  class ArgumentList : public ASTNode {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ArgumentList(const std::shared_ptr<SyntaxNode> &SN)
        : ASTNode(SN) {}
    /// Get the argument list.
    auto getArguments() const { return findMany<ASTExpr>(isExprSyntaxKind); }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ArgumentList>(SN, SyntaxKind::CallExprArgumentList);
    }
  };

  explicit ASTCallExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTExpr(SN) {}
  /// Get the expression that is being called
  auto getCallee() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  /// Get the type arguments provided to this call.
  auto getTypeArgumentList() const {
    return findSingle<
        ASTTypeArgumentListFragment<SyntaxKind::CallExprTypeArgumentList>>(
        SyntaxKind::CallExprTypeArgumentList);
  }

  /// Get the arguments provided to this call.
  auto getArgumentList() const {
    return findSingle<ArgumentList>(SyntaxKind::CallExprArgumentList);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::CallExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTCallExpr>(SN, SyntaxKind::CallExpr);
  }
};

class ASTConstructionExpr : public ASTExpr {
public:
  /// Member class representing a single member. This is here because each
  /// member is a tuple of (name, value) and cannot be represented like an atom
  /// in the same way CallExpr arguments can.
  class ConstructionMember : public ASTNode {
  public:
    explicit ConstructionMember(const std::shared_ptr<SyntaxNode> &SN)
        : ASTNode(SN) {}
    /// Get the member name
    auto getName() const {
      return findSingle<Identifier>(SyntaxKind::Identifier);
    }

    /// Get the value
    auto getValue() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ConstructionMember>(SN, SyntaxKind::ConstructionExprMember);
    }
  };

  /// Member class representing the set of values being initialized into the
  /// struct.
  class ConstructionMemberList : public ASTNode {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ConstructionMemberList(const std::shared_ptr<SyntaxNode> &SN)
        : ASTNode(SN) {}
    /// Get the members.
    auto getMembers() const {
      return findMany<ConstructionMember>(SyntaxKind::ConstructionExprMember);
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ConstructionMemberList>(
          SN, SyntaxKind::ConstructionExprMemberList);
    }
  };

  explicit ASTConstructionExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
  /// Get the construction initializer member list.
  auto getMemberList() const {
    return findSingle<ConstructionMemberList>(
        SyntaxKind::ConstructionExprMemberList);
  }

  /// Get the type being constructed
  auto getConstructorType() const {
    return findSingle<ASTType>(isTypeSyntaxKind);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ConstructionExpr;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTConstructionExpr>(SN, SyntaxKind::ConstructionExpr);
  }
};

class ASTStmt : public ASTNode {
public:
  explicit ASTStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isStmtSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTStmt>(SN, isStmtSyntaxKind);
  }
};

/// Member class for a list of statements.
template <SyntaxKind ChildKind> class ASTBodyFragment : public ASTNode {
public:
  explicit ASTBodyFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the statement list.
  auto getStmtList() const { return findMany<ASTStmt>(isStmtSyntaxKind); }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTBodyFragment>(SN, ChildKind);
  }
};

class ASTLetStmt : public ASTStmt {
public:
  explicit ASTLetStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the name of the let binding.
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  /// Get the optional type annotation of the let binding.
  auto getTypeAnnotation() const {
    return findSingle<ASTType>(isTypeSyntaxKind);
  }

  /// Get the initializer of the let binding.
  auto getInitializerExpr() const {
    return findSingle<ASTExpr>(isExprSyntaxKind);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::LetStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTLetStmt>(SN, SyntaxKind::LetStmt);
  }
};

class ASTIfStmt : public ASTStmt {
public:
  explicit ASTIfStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the condition of the if statement
  auto getConditionExpr() const {
    return findSingle<ASTExpr>(isExprSyntaxKind);
  }

  /// Get the body that executes if the condition is true.
  auto getThenBody() const {
    return findSingle<ASTBodyFragment<SyntaxKind::IfThenBody>>(
        SyntaxKind::IfThenBody);
  }

  /// Get the body that executes if the condition is false.
  auto getElseBody() const {
    return findSingle<ASTBodyFragment<SyntaxKind::IfElseBody>>(
        SyntaxKind::IfElseBody);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IfStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTIfStmt>(SN, SyntaxKind::IfStmt);
  }
};

class ASTForStmt : public ASTStmt {
public:
  /// Member class for the initializer
  class Initializer : public ASTNode {
  public:
    explicit Initializer(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get the binding variable name.
    auto getName() const {
      return findSingle<Identifier>(SyntaxKind::Identifier);
    }

    /// Get the type annotation on the binding.
    auto getTypeAnnotation() const {
      return findSingle<ASTType>(isTypeSyntaxKind);
    }

    /// Get the initializer expression for the binding.
    auto getInitializer() const {
      return findSingle<ASTExpr>(isExprSyntaxKind);
    }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Initializer>(SN, SyntaxKind::ForInitializer);
    }
  };

  /// Member class for the condition
  class Condition : public ASTNode {
  public:
    explicit Condition(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get the condition expression.
    auto getExpr() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Condition>(SN, SyntaxKind::ForCondition);
    }
  };

  /// Member class for the increment
  class Increment : public ASTNode {
  public:
    explicit Increment(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get the increment expression.
    auto getExpr() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Increment>(SN, SyntaxKind::ForIncrement);
    }
  };

  explicit ASTForStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the initializer.
  auto getInitializer() const {
    return findSingle<Initializer>(SyntaxKind::ForInitializer);
  }

  /// Get the condition.
  auto getCondition() const {
    return findSingle<Condition>(SyntaxKind::ForCondition);
  }

  /// Get the increment
  auto getIncrement() const {
    return findSingle<Increment>(SyntaxKind::ForIncrement);
  }

  /// Get the body
  auto getBody() const {
    return findSingle<ASTBodyFragment<SyntaxKind::ForBody>>(
        SyntaxKind::ForBody);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ForStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTForStmt>(SN, SyntaxKind::ForStmt);
  }
};

class ASTBreakStmt : public ASTStmt {
public:
  explicit ASTBreakStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::BreakStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTBreakStmt>(SN, SyntaxKind::BreakStmt);
  }
};

class ASTContinueStmt : public ASTStmt {
public:
  explicit ASTContinueStmt(const std::shared_ptr<SyntaxNode> &SN)
      : ASTStmt(SN) {}

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ContinueStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTContinueStmt>(SN, SyntaxKind::ContinueStmt);
  }
};

class ASTReturnStmt : public ASTStmt {
public:
  explicit ASTReturnStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the optional return value.
  auto getReturnExpr() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ReturnStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTReturnStmt>(SN, SyntaxKind::ReturnStmt);
  }
};

class ASTExprStmt : public ASTStmt {
public:
  explicit ASTExprStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the expression.
  auto getExpr() const { return findSingle<ASTExpr>(isExprSyntaxKind); }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ExprStmt;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTExprStmt>(SN, SyntaxKind::ExprStmt);
  }
};

class ASTDecl : public ASTNode {
public:
  explicit ASTDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}

  static bool classof(const ASTNode *Node) {
    return isDeclSyntaxKind(Node->getSyntaxKind());
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTDecl>(SN, isDeclSyntaxKind);
  }
};

class ASTPackageDecl : public ASTDecl {
public:
  explicit ASTPackageDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the name of the package.
  auto getName() const { return findMany<Identifier>(SyntaxKind::Identifier); }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::PackageDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTPackageDecl>(SN, SyntaxKind::PackageDecl);
  }
};

class ASTImportDecl : public ASTDecl {
public:
  explicit ASTImportDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the name this declaration imports into scope.
  auto getImportedName() const {
    return findMany<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ImportDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTImportDecl>(SN, SyntaxKind::ImportDecl);
  }
};

/// Member class for a single type parameter.
template <SyntaxKind ChildKind>
class ASTTypeParameterFragment : public ASTNode {
public:
  explicit ASTTypeParameterFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the name of the type parameter
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTTypeParameterFragment>(SN, ChildKind);
  }
};

/// Member class for the type parameter list
template <SyntaxKind ListKind, SyntaxKind ChildKind>
class ASTTypeParameterListFragment : public ASTNode {
public:
  explicit ASTTypeParameterListFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the type parameters
  auto getTypeParameters() const {
    return findMany<ASTTypeParameterFragment<ChildKind>>(ChildKind);
  }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTTypeParameterListFragment>(SN, ListKind);
  }
};

/// Member class for a single parameter.
template <SyntaxKind ChildKind> class ASTParameterFragment : public ASTNode {
public:
  explicit ASTParameterFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the name of the parameter
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  /// Get the type annotation of the parameter.
  auto getTypeAnnotation() const { return findMany<ASTType>(isTypeSyntaxKind); }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTParameterFragment>(SN, ChildKind);
  }
};

/// Member class for the parameter list.
template <SyntaxKind ListKind, SyntaxKind ChildKind>
class ASTParameterListFragment : public ASTNode {
public:
  explicit ASTParameterListFragment(const std::shared_ptr<SyntaxNode> &SN)
      : ASTNode(SN) {}
  /// Get the parameter list
  auto getParameters() const {
    return findMany<ASTParameterFragment<ChildKind>>(ChildKind);
  }

  static bool classof(const ASTNode *) { return false; }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ASTParameterListFragment>(SN, ListKind);
  }
};

class ASTFunctionDecl : public ASTDecl {
public:
  explicit ASTFunctionDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the optionally declared return type
  auto getReturnTypeAnnotation() const {
    return findSingle<ASTType>(isTypeSyntaxKind);
  }

  /// Get the type parameter list
  auto getTypeParameterList() const {
    return findSingle<
        ASTTypeParameterListFragment<SyntaxKind::FunctionTypeParameterList,
                                     SyntaxKind::FunctionTypeParameter>>(
        SyntaxKind::FunctionTypeParameterList);
  }

  /// Get the parameter list
  auto getParameterList() const {
    return findSingle<ASTParameterListFragment<
        SyntaxKind::FunctionParameterList, SyntaxKind::FunctionParameter>>(
        SyntaxKind::FunctionParameterList);
  }

  /// Get the function body
  auto getBody() const {
    return findSingle<ASTBodyFragment<SyntaxKind::FunctionBody>>(
        SyntaxKind::FunctionBody);
  }

  /// Is this function intrinsic?
  auto isIntrinsic() const -> bool {
    return getSyntaxKind() == SyntaxKind::IntrinsicFunctionDecl;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::FunctionDecl ||
           Node->getSyntaxKind() == SyntaxKind::IntrinsicFunctionDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTFunctionDecl>(SN, [](SyntaxKind SK) {
      return SK == SyntaxKind::IntrinsicFunctionDecl ||
             SK == SyntaxKind::FunctionDecl;
    });
  }
};

class ASTStructDecl : public ASTDecl {
public:
  /// Member class for a single struct member.
  class Member : public ASTNode {
  public:
    explicit Member(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get the name of the member.
    auto getName() const {
      return findSingle<Identifier>(SyntaxKind::Identifier);
    }

    /// Get the type annotation for the member.
    auto getTypeAnnotation() const {
      return findSingle<ASTType>(isTypeSyntaxKind);
    }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Member>(SN, SyntaxKind::StructMember);
    }
  };

  /// Member class for the struct member list.
  class MemberList : public ASTNode {
  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get the member list
    auto getMembers() const {
      return findMany<Member>(SyntaxKind::StructMember);
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::StructMemberList);
    }
  };

  explicit ASTStructDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the name of the struct
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  /// Get the member list
  auto getMemberList() const {
    return findSingle<MemberList>(SyntaxKind::StructMemberList);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::StructDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTStructDecl>(SN, SyntaxKind::StructDecl);
  }
};

class ASTIntrinsicTypeDecl : public ASTDecl {
public:
  explicit ASTIntrinsicTypeDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the name of the type decl
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IntrinsicTypeDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTIntrinsicTypeDecl>(SN, SyntaxKind::IntrinsicTypeDecl);
  }
};

class ASTTraitDecl : public ASTDecl {
public:
  class FunctionMember : public ASTNode {
  public:
    explicit FunctionMember(const std::shared_ptr<SyntaxNode> &SN)
        : ASTNode(SN) {}
    /// Get the function name.
    auto getName() const {
      return findSingle<Identifier>(SyntaxKind::Identifier);
    }

    /// Get the type parameters declared on the function.
    auto getTypeParameterList() const {
      return findSingle<
          ASTTypeParameterListFragment<SyntaxKind::FunctionTypeParameterList,
                                       SyntaxKind::FunctionTypeParameter>>(
          SyntaxKind::FunctionTypeParameterList);
    }

    /// Get the parameters declared on the function
    auto getParameterList() const {
      return findSingle<ASTParameterListFragment<
          SyntaxKind::FunctionParameterList, SyntaxKind::FunctionParameter>>(
          SyntaxKind::FunctionParameterList);
    }

    /// Get the optionally declared return type
    auto getReturnTypeAnnotation() const {
      return findSingle<ASTType>(isTypeSyntaxKind);
    }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<FunctionMember>(SN, SyntaxKind::TraitFunctionMember);
    }
  };

  /// Member class for the list of trait members.
  class MemberList : public ASTNode {
  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get all function members
    auto getFunctionMembers() const {
      return findMany<FunctionMember>(SyntaxKind::TraitFunctionMember);
    }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::TraitMemberList);
    }
  };

  explicit ASTTraitDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the trait name.
  auto getName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  /// Get the list of type parameters on the trait.
  auto getTypeParameterList() const {
    return findSingle<ASTTypeParameterListFragment<
        SyntaxKind::TraitTypeParameterList, SyntaxKind::TraitTypeParameter>>(
        SyntaxKind::TraitTypeParameterList);
  }

  /// Get the member list.
  auto getMemberList() const {
    return findSingle<MemberList>(SyntaxKind::TraitMemberList);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::TraitDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTTraitDecl>(SN, SyntaxKind::TraitDecl);
  }
};

class ASTInstanceDecl : public ASTDecl {
public:
  /// Member class for the trait members
  class MemberList : public ASTNode {
  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : ASTNode(SN) {}
    /// Get all regular function members.
    auto getFunctionMembers() const {
      return findMany<ASTFunctionDecl>([](SyntaxKind SK) {
        return SK == SyntaxKind::FunctionDecl ||
               SK == SyntaxKind::IntrinsicFunctionDecl;
      });
    }

    static bool classof(const ASTNode *) { return false; }
    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::InstanceMemberList);
    }
  };

  explicit ASTInstanceDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the type this instance is attached to.
  auto getAttachedType() const { return findSingle<ASTType>(isTypeSyntaxKind); }

  /// Get the type arguments provided to the instance.
  auto getTypeArgumentList() const {
    return findSingle<
        ASTTypeArgumentListFragment<SyntaxKind::InstanceTypeArgumentList>>(
        SyntaxKind::InstanceTypeArgumentList);
  }

  /// Get the trait this is an instance of.
  auto getTraitName() const {
    return findSingle<Identifier>(SyntaxKind::Identifier);
  }

  /// Get the instance member list.
  auto getMemberList() const {
    return findSingle<MemberList>(SyntaxKind::InstanceMemberList);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::InstanceDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTInstanceDecl>(SN, SyntaxKind::InstanceDecl);
  }
};

class ASTModuleDecl : public ASTDecl {
public:
  explicit ASTModuleDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the package name of the module.
  auto getPackageName() const {
    return findSingle<ASTPackageDecl>(SyntaxKind::PackageDecl);
  }

  /// Get the import declarations for the module.
  auto getImportDeclarations() const {
    return findMany<ASTImportDecl>(SyntaxKind::ImportDecl);
  }

  /// Get the function declarations for the module.
  auto getFunctionDeclarations() const {
    return findMany<ASTFunctionDecl>(SyntaxKind::FunctionDecl);
  }

  /// Get the struct declarations for the module.
  auto getStructDeclarations() const {
    return findMany<ASTStructDecl>(SyntaxKind::StructDecl);
  }

  /// Get the intrinsic type declarations for the module.
  auto getIntrinsicTypeDeclarations() const {
    return findMany<ASTIntrinsicTypeDecl>(SyntaxKind::IntrinsicTypeDecl);
  }

  /// Get the trait declarations for the module.
  auto getTraitDeclarations() const {
    return findMany<ASTTraitDecl>(SyntaxKind::TraitDecl);
  }

  /// Get the instance declarations for the module.
  auto getInstanceDeclarations() const {
    return findMany<ASTInstanceDecl>(SyntaxKind::InstanceDecl);
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::ModuleDecl;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTModuleDecl>(SN, SyntaxKind::ModuleDecl);
  }
};
} // namespace xd

#endif // XD_FRONTEND_AST_H
