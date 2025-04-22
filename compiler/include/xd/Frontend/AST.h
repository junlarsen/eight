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

  /// Factory function for automatic casting
  template <class T>
  static auto from(const std::shared_ptr<SyntaxNode> &SN,
                   const std::function<bool(SyntaxKind)> &Predicate)
      -> std::optional<std::shared_ptr<T>> {
    if (!Predicate(SN->getSyntaxKind()) || !SN->isNode())
      return std::nullopt;
    return std::make_shared<T>(SN);
  }

  /// Factory function for automatic casting
  template <class T>
  static auto from(const std::shared_ptr<SyntaxNode> &SN,
                   SyntaxKind SK) -> std::optional<std::shared_ptr<T>> {
    if (SN->getSyntaxKind() != SK || !SN->isNode())
      return std::nullopt;
    return std::make_shared<T>(SN);
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
  auto getInnerType() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto Inner = SN->findChild(isTypeSyntaxKind); Inner.has_value())
      return ASTType::cast(*Inner);
    return std::nullopt;
  }

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
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
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
template <SyntaxKind ListKind> class TypeArgumentList {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit TypeArgumentList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
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

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<TypeArgumentList>(SN, ListKind);
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
  auto getOperand() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Operand = SN->findChild(isExprSyntaxKind); Operand.has_value())
      return ASTExpr::cast(*Operand);
    return std::nullopt;
  }

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
  auto getInnerExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto InnerExpr = SN->findChildAtIndex(isExprSyntaxKind, 0);
        InnerExpr.has_value())
      return ASTExpr::cast(*InnerExpr);
    return std::nullopt;
  }

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
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTConstantIndexExpr>(SN, SyntaxKind::ConstantIndexExpr);
  }
};

class ASTReferenceExpr : public ASTExpr {
public:
  explicit ASTReferenceExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
  /// Get the variable name for this reference expression.
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Name = SN->findChild(SyntaxKind::Identifier); Name.has_value())
      return Identifier::cast(*Name);
    return std::nullopt;
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
      auto LitTok = llvm::dyn_cast<GreenToken>((*Lit)->getGreen().get());
      assert(LitTok != nullptr && "integer literal node was not a token");
      return llvm::APInt(32, LitTok->getText(), 10);
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
  class ArgumentList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ArgumentList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
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

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ArgumentList>(SN, SyntaxKind::CallExprArgumentList);
    }
  };

  explicit ASTCallExpr(const std::shared_ptr<SyntaxNode> &SN) : ASTExpr(SN) {}
  /// Get the expression that is being called
  auto getCallee() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Callee = SN->findChild(isExprSyntaxKind); Callee.has_value())
      return ASTExpr::cast(*Callee);
    return std::nullopt;
  }

  /// Get the type arguments provided to this call.
  auto getTypeArgumentList() const
      -> std::optional<std::shared_ptr<
          TypeArgumentList<SyntaxKind::CallExprTypeArgumentList>>> {
    if (auto TAL = SN->findChild(SyntaxKind::CallExprTypeArgumentList);
        TAL.has_value())
      return TypeArgumentList<SyntaxKind::CallExprTypeArgumentList>::cast(*TAL);
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
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTCallExpr>(SN, SyntaxKind::CallExpr);
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
    explicit ConstructionMember(const std::shared_ptr<SyntaxNode> &SN)
        : SN(SN) {}
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

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ConstructionMember>(SN, SyntaxKind::ConstructionExprMember);
    }
  };

  /// Member class representing the set of values being initialized into the
  /// struct.
  class ConstructionMemberList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit ConstructionMemberList(const std::shared_ptr<SyntaxNode> &SN)
        : SN(SN) {}
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

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<ConstructionMemberList>(
          SN, SyntaxKind::ConstructionExprMemberList);
    }
  };

  explicit ASTConstructionExpr(const std::shared_ptr<SyntaxNode> &SN)
      : ASTExpr(SN) {}
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
template <SyntaxKind ChildKind> class Body {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit Body(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  /// Get the statement list.
  auto
  getStmtList() const -> std::optional<std::vector<std::shared_ptr<ASTStmt>>> {
    if (auto SL = SN->findChildren(isStmtSyntaxKind); SL.has_value()) {
      std::vector<std::shared_ptr<ASTStmt>> Result;
      for (auto Stmt : *SL)
        if (auto S = ASTStmt::cast(Stmt); S.has_value())
          Result.push_back(*S);
      return Result;
    }
    return std::nullopt;
  }

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<Body>(SN, ChildKind);
  }
};

class ASTLetStmt : public ASTStmt {
public:
  explicit ASTLetStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
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
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTLetStmt>(SN, SyntaxKind::LetStmt);
  }
};

class ASTIfStmt : public ASTStmt {
public:
  explicit ASTIfStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the condition of the if statement
  auto getConditionExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
      return ASTExpr::cast(*Expr);
    return std::nullopt;
  }

  /// Get the body that executes if the condition is true.
  auto getThenBody() const
      -> std::optional<std::shared_ptr<Body<SyntaxKind::IfThenBody>>> {
    if (auto TB = SN->findChild(SyntaxKind::IfThenBody); TB.has_value())
      return Body<SyntaxKind::IfThenBody>::cast(*TB);
    return std::nullopt;
  }

  /// Get the body that executes if the condition is false.
  auto getElseBody() const
      -> std::optional<std::shared_ptr<Body<SyntaxKind::IfElseBody>>> {
    if (auto EB = SN->findChild(SyntaxKind::IfElseBody); EB.has_value())
      return Body<SyntaxKind::IfElseBody>::cast(*EB);
    return std::nullopt;
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
  class Initializer {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit Initializer(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the binding variable name.
    auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
      if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
        return Identifier::cast(*Ident);
      return std::nullopt;
    }

    /// Get the type annotation on the binding.
    auto getTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
      if (auto T = SN->findChild(isTypeSyntaxKind); T.has_value())
        return ASTType::cast(*T);
      return std::nullopt;
    }

    /// Get the initializer expression for the binding.
    auto getInitializer() const -> std::optional<std::shared_ptr<ASTExpr>> {
      if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
        return ASTExpr::cast(*Expr);
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Initializer>(SN, SyntaxKind::ForInitializer);
    }
  };

  /// Member class for the condition
  class Condition {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit Condition(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the condition expression.
    auto getExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
      if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
        return ASTExpr::cast(*Expr);
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Condition>(SN, SyntaxKind::ForCondition);
    }
  };

  /// Member class for the increment
  class Increment {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit Increment(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the increment expression.
    auto getExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
      if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
        return ASTExpr::cast(*Expr);
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Increment>(SN, SyntaxKind::ForIncrement);
    }
  };

  explicit ASTForStmt(const std::shared_ptr<SyntaxNode> &SN) : ASTStmt(SN) {}
  /// Get the initializer.
  auto getInitializer() const -> std::optional<std::shared_ptr<Initializer>> {
    if (auto I = SN->findChild(SyntaxKind::ForInitializer); I.has_value())
      return Initializer::cast(*I);
    return std::nullopt;
  }

  /// Get the condition.
  auto getCondition() const -> std::optional<std::shared_ptr<Condition>> {
    if (auto Cond = SN->findChild(SyntaxKind::ForCondition); Cond.has_value())
      return Condition::cast(*Cond);
    return std::nullopt;
  }

  /// Get the increment
  auto getIncrement() const -> std::optional<std::shared_ptr<Increment>> {
    if (auto I = SN->findChild(SyntaxKind::ForIncrement); I.has_value())
      return Increment::cast(*I);
    return std::nullopt;
  }

  /// Get the body
  auto
  getBody() const -> std::optional<std::shared_ptr<Body<SyntaxKind::ForBody>>> {
    if (auto B = SN->findChild(SyntaxKind::ForBody); B.has_value())
      return Body<SyntaxKind::ForBody>::cast(*B);
    return std::nullopt;
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
  auto getReturnExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
      return ASTExpr::cast(*Expr);
    return std::nullopt;
  }

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
  auto getExpr() const -> std::optional<std::shared_ptr<ASTExpr>> {
    if (auto Expr = SN->findChild(isExprSyntaxKind); Expr.has_value())
      return ASTExpr::cast(*Expr);
    return std::nullopt;
  }

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

/// Member class for a single type parameter.
template <SyntaxKind ChildKind> class TypeParameter {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit TypeParameter(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  /// Get the name of the type parameter
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return std::make_shared<Identifier>(*Ident);
    return std::nullopt;
  }

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<TypeParameter>(SN, ChildKind);
  }
};

/// Member class for the type parameter list
template <SyntaxKind ListKind, SyntaxKind ChildKind> class TypeParameterList {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit TypeParameterList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  /// Get the type parameters
  auto getTypeParameters() const
      -> std::optional<std::vector<std::shared_ptr<TypeParameter<ChildKind>>>> {
    if (auto TPS = SN->findChildren(ChildKind); TPS.has_value()) {
      std::vector<std::shared_ptr<TypeParameter<ChildKind>>> Result;
      for (auto TP : *TPS) {
        if (auto T = TypeParameter<ChildKind>::cast(TP); T.has_value())
          Result.push_back(*T);
      }
      return Result;
    }
    return std::nullopt;
  }

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<TypeParameterList>(SN, ListKind);
  }
};

/// Member class for a single parameter.
template <SyntaxKind ChildKind> class Parameter {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit Parameter(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  /// Get the name of the parameter
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return std::make_shared<Identifier>(*Ident);
    return std::nullopt;
  }

  /// Get the type annotation of the parameter.
  auto getTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto T = SN->findChild(isTypeSyntaxKind); T.has_value())
      return ASTType::cast(*T);
    return std::nullopt;
  }

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<Parameter>(SN, ChildKind);
  }
};

/// Member class for the parameter list.
template <SyntaxKind ListKind, SyntaxKind ChildKind> class ParameterList {
  std::shared_ptr<SyntaxNode> SN;

public:
  explicit ParameterList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
  /// Get the parameter list
  auto getParameters() const
      -> std::optional<std::vector<std::shared_ptr<Parameter<ChildKind>>>> {
    if (auto TPS = SN->findChildren(ChildKind); TPS.has_value()) {
      std::vector<std::shared_ptr<Parameter<ChildKind>>> Result;
      for (auto TP : *TPS) {
        if (auto T = Parameter<ChildKind>::cast(TP); T.has_value())
          Result.push_back(*T);
      }
      return Result;
    }
    return std::nullopt;
  }

  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return ASTNode::from<ParameterList>(SN, ListKind);
  }
};

class ASTFunctionDecl : public ASTDecl {
public:
  explicit ASTFunctionDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the optionally declared return type
  auto
  getReturnTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto Type = SN->findChild(isTypeSyntaxKind); Type.has_value())
      return ASTType::cast(*Type);
    return std::nullopt;
  }

  /// Get the type parameter list
  auto getTypeParameterList() const
      -> std::optional<std::shared_ptr<
          TypeParameterList<SyntaxKind::FunctionTypeParameterList,
                            SyntaxKind::FunctionTypeParameter>>> {
    if (auto TPS = SN->findChild(SyntaxKind::FunctionTypeParameterList);
        TPS.has_value())
      return TypeParameterList<SyntaxKind::FunctionTypeParameterList,
                               SyntaxKind::FunctionTypeParameter>::cast(*TPS);
    return std::nullopt;
  }

  /// Get the parameter list
  auto getParameterList() const
      -> std::optional<std::shared_ptr<ParameterList<
          SyntaxKind::FunctionParameterList, SyntaxKind::FunctionParameter>>> {
    if (auto PS = SN->findChild(SyntaxKind::FunctionParameterList);
        PS.has_value())
      return ParameterList<SyntaxKind::FunctionParameterList,
                           SyntaxKind::FunctionParameter>::cast(*PS);
    return std::nullopt;
  }

  /// Get the function body
  auto getBody() const
      -> std::optional<std::shared_ptr<Body<SyntaxKind::FunctionBody>>> {
    if (auto B = SN->findChild(SyntaxKind::FunctionBody); B.has_value())
      return Body<SyntaxKind::FunctionBody>::cast(*B);
    return std::nullopt;
  }

  /// Is this function intrinsic?
  auto isIntrinsic() const -> bool {
    return getSyntaxKind() == SyntaxKind::IntrinsicFunction;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::Function ||
           Node->getSyntaxKind() == SyntaxKind::IntrinsicFunction;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTFunctionDecl>(SN, [](SyntaxKind SK) {
      return SK == SyntaxKind::IntrinsicFunction || SK == SyntaxKind::Function;
    });
  }
};

class ASTStructDecl : public ASTDecl {
public:
  /// Member class for a single struct member.
  class Member {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit Member(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the name of the member.
    auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
      if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
        return Identifier::cast(*Ident);
      return std::nullopt;
    }

    /// Get the type annotation for the member.
    auto getTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
      if (auto T = SN->findChild(isTypeSyntaxKind); T.has_value())
        return ASTType::cast(*T);
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<Member>(SN, SyntaxKind::StructMember);
    }
  };

  /// Member class for the struct member list.
  class MemberList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the member list
    auto
    getMembers() const -> std::optional<std::vector<std::shared_ptr<Member>>> {
      if (auto MS = SN->findChildren(SyntaxKind::StructMember);
          MS.has_value()) {
        std::vector<std::shared_ptr<Member>> Result;
        for (auto M : *MS)
          if (auto MN = Member::cast(M); MN.has_value())
            Result.push_back(*MN);
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::StructMemberList);
    }
  };

  explicit ASTStructDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the name of the struct
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
  }

  /// Get the member list
  auto getMemberList() const -> std::optional<std::shared_ptr<MemberList>> {
    if (auto ML = SN->findChild(SyntaxKind::StructMemberList); ML.has_value())
      return MemberList::cast(*ML);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::Struct;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTStructDecl>(SN, SyntaxKind::Struct);
  }
};

class ASTIntrinsicTypeDecl : public ASTDecl {
public:
  explicit ASTIntrinsicTypeDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the name of the type decl
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::IntrinsicType;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTIntrinsicTypeDecl>(SN, SyntaxKind::IntrinsicType);
  }
};

class ASTTraitDecl : public ASTDecl {
public:
  class FunctionMember {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit FunctionMember(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get the function name.
    auto getName() -> std::optional<std::shared_ptr<Identifier>> {
      if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
        return Identifier::cast(*Ident);
      return std::nullopt;
    }

    /// Get the type parameters declared on the function.
    auto getTypeParameterList() const
        -> std::optional<std::shared_ptr<
            TypeParameterList<SyntaxKind::FunctionTypeParameterList,
                              SyntaxKind::FunctionTypeParameter>>> {
      if (auto TPS = SN->findChild(SyntaxKind::FunctionTypeParameterList);
          TPS.has_value())
        return TypeParameterList<SyntaxKind::FunctionTypeParameterList,
                                 SyntaxKind::FunctionTypeParameter>::cast(*TPS);
      return std::nullopt;
    }

    /// Get the parameters declared on the function
    auto getParameterList() const
        -> std::optional<
            std::shared_ptr<ParameterList<SyntaxKind::FunctionParameterList,
                                          SyntaxKind::FunctionParameter>>> {
      if (auto PS = SN->findChild(SyntaxKind::FunctionParameterList);
          PS.has_value())
        return ParameterList<SyntaxKind::FunctionParameterList,
                             SyntaxKind::FunctionParameter>::cast(*PS);
      return std::nullopt;
    }

    /// Get the optionally declared return type
    auto
    getReturnTypeAnnotation() const -> std::optional<std::shared_ptr<ASTType>> {
      if (auto RT = SN->findChild(isTypeSyntaxKind); RT.has_value())
        return ASTType::cast(*RT);
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<FunctionMember>(SN, SyntaxKind::TraitFunctionMember);
    }
  };

  /// Member class for the list of trait members.
  class MemberList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get all function members
    auto getFunctionMembers() const
        -> std::optional<std::vector<std::shared_ptr<FunctionMember>>> {
      if (auto MS = SN->findChildren(SyntaxKind::TraitFunctionMember);
          MS.has_value()) {
        std::vector<std::shared_ptr<FunctionMember>> Result;
        for (auto M : *MS)
          if (auto MN = FunctionMember::cast(M); MN.has_value())
            Result.push_back(*MN);
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::TraitMemberList);
    }
  };

  explicit ASTTraitDecl(const std::shared_ptr<SyntaxNode> &SN) : ASTDecl(SN) {}
  /// Get the trait name.
  auto getName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto Ident = SN->findChild(SyntaxKind::Identifier); Ident.has_value())
      return Identifier::cast(*Ident);
    return std::nullopt;
  }

  /// Get the list of type parameters on the trait.
  auto getTypeParameterList() const
      -> std::optional<
          std::shared_ptr<TypeParameterList<SyntaxKind::TraitTypeParameterList,
                                            SyntaxKind::TraitTypeParameter>>> {
    if (auto TPS = SN->findChild(SyntaxKind::TraitTypeParameterList);
        TPS.has_value())
      return TypeParameterList<SyntaxKind::TraitTypeParameterList,
                               SyntaxKind::TraitTypeParameter>::cast(*TPS);
    return std::nullopt;
  }

  /// Get the member list.
  auto getMemberList() const -> std::optional<std::shared_ptr<MemberList>> {
    if (auto MS = SN->findChild(SyntaxKind::TraitMemberList); MS.has_value())
      return MemberList::cast(*MS);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::Trait;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTTraitDecl>(SN, SyntaxKind::Trait);
  }
};

class ASTInstanceDecl : public ASTDecl {
public:
  /// Member class for the trait members
  class MemberList {
    std::shared_ptr<SyntaxNode> SN;

  public:
    explicit MemberList(const std::shared_ptr<SyntaxNode> &SN) : SN(SN) {}
    /// Get all regular function members.
    auto getFunctionMembers() const
        -> std::optional<std::vector<std::shared_ptr<ASTFunctionDecl>>> {
      if (auto MS = SN->findChildren([&](SyntaxKind SK) {
            return SK == SyntaxKind::Function ||
                   SK == SyntaxKind::IntrinsicFunction;
          });
          MS.has_value()) {
        std::vector<std::shared_ptr<ASTFunctionDecl>> Result;
        for (auto M : *MS)
          if (auto MM = ASTFunctionDecl::cast(M); MM.has_value())
            Result.push_back(*MM);
        return Result;
      }
      return std::nullopt;
    }

    static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
      return from<MemberList>(SN, SyntaxKind::InstanceMemberList);
    }
  };

  explicit ASTInstanceDecl(const std::shared_ptr<SyntaxNode> &SN)
      : ASTDecl(SN) {}
  /// Get the type this instance is attached to.
  auto getAttachedType() const -> std::optional<std::shared_ptr<ASTType>> {
    if (auto T = SN->findChild(isTypeSyntaxKind); T.has_value())
      return ASTType::cast(*T);
    return std::nullopt;
  }

  /// Get the type arguments provided to the instance.
  auto getTypeArgumentList() const
      -> std::optional<std::shared_ptr<
          TypeArgumentList<SyntaxKind::InstanceTypeArgumentList>>> {
    if (auto TAL = SN->findChild(SyntaxKind::InstanceTypeArgumentList);
        TAL.has_value())
      return TypeArgumentList<SyntaxKind::InstanceTypeArgumentList>::cast(*TAL);
    return std::nullopt;
  }

  /// Get the trait this is an instance of.
  auto getTraitName() const -> std::optional<std::shared_ptr<Identifier>> {
    if (auto T = SN->findChild(SyntaxKind::Identifier); T.has_value())
      return Identifier::cast(*T);
    return std::nullopt;
  }

  /// Get the instance member list.
  auto getMemberList() const -> std::optional<std::shared_ptr<MemberList>> {
    if (auto ML = SN->findChild(SyntaxKind::InstanceMemberList); ML.has_value())
      return MemberList::cast(*ML);
    return std::nullopt;
  }

  static bool classof(const ASTNode *Node) {
    return Node->getSyntaxKind() == SyntaxKind::Instance;
  }
  static auto cast(const std::shared_ptr<SyntaxNode> &SN) {
    return from<ASTInstanceDecl>(SN, SyntaxKind::Instance);
  }
};
} // namespace xd

#endif // XD_FRONTEND_AST_H
