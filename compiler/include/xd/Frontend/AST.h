//===----- AST ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef AST_H
#define AST_H

#include "xd/Frontend/Lexer.h"

#include <memory>
#include <vector>

namespace xd {
class ASTIntegerLiteralExpr;
class ASTBooleanLiteralExpr;
class ASTAssignmentExpr;
class ASTBinaryOperatorExpr;

class Identifier {
  std::string Name;
  SourceLocation Loc;

public:
  Identifier(std::string Name, SourceLocation Loc) : Name(Name), Loc(Loc) {}
  std::string getName() const { return Name; }
  SourceLocation getLoc() const { return Loc; }
};

enum class ASTNodeKind {
  IntegerLiteralExpr,
  BooleanLiteralExpr,
  AssignmentExpr,
  BinaryOperatorExpr,
  UnaryOperatorExpr,
  ConstantIndexExpr,
  VariableIndexExpr,
  ReferenceExpr,
  CallExpr,
  ConstructionExpr,
  GroupingExpr,
};

class ASTNode {
  const ASTNodeKind Kind;
  SourceLocation Loc;

public:
  ASTNode(ASTNodeKind Kind, SourceLocation Loc) : Kind(Kind), Loc(Loc) {}
  ASTNodeKind getKind() const { return Kind; }
  SourceLocation getLoc() const { return Loc; }
};

class ASTIntegerLiteralExpr : public ASTNode {
  llvm::APInt Value;

public:
  ASTIntegerLiteralExpr(SourceLocation Loc, llvm::APInt Value)
      : ASTNode(ASTNodeKind::IntegerLiteralExpr, Loc), Value(Value) {}

  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::IntegerLiteralExpr;
  }
};

class ASTBooleanLiteralExpr : public ASTNode {
  llvm::APInt Value;

public:
  ASTBooleanLiteralExpr(SourceLocation Loc, llvm::APInt Value)
      : ASTNode(ASTNodeKind::BooleanLiteralExpr, Loc), Value(Value) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::BooleanLiteralExpr;
  }
};

class ASTAssignmentExpr : public ASTNode {
  std::unique_ptr<ASTNode> Destination;
  std::unique_ptr<ASTNode> Value;

public:
  ASTAssignmentExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Destination,
                    std::unique_ptr<ASTNode> Value)
      : ASTNode(ASTNodeKind::AssignmentExpr, Loc),
        Destination(std::move(Destination)), Value(std::move(Value)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::AssignmentExpr;
  }
};

enum class ASTBinaryOperatorKind : uint8_t {
  Addition,
  Subtraction,
  Multiplication,
  Division,
  Remainder,
  Equality,
  Inequality,
  LessThan,
  LessThanOrEqual,
  GreaterThan,
  GreaterThanOrEqual,
  LogicalAnd,
  LogicalOr,
};

class ASTBinaryOperatorExpr : public ASTNode {
  std::unique_ptr<ASTNode> LHS;
  std::unique_ptr<ASTNode> RHS;
  ASTBinaryOperatorKind Op;

public:
  ASTBinaryOperatorExpr(SourceLocation Loc, std::unique_ptr<ASTNode> LHS,
                        ASTBinaryOperatorKind Op)
      : ASTNode(ASTNodeKind::BinaryOperatorExpr, Loc), LHS(std::move(LHS)),
        Op(Op) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::BinaryOperatorExpr;
  }
};

enum class ASTUnaryOperatorKind : uint8_t {
  LogicalNot,
  Negative,
  Dereference,
  AddressOf,
};

class ASTUnaryOperatorExpr : public ASTNode {
  std::unique_ptr<ASTNode> Operand;
  ASTUnaryOperatorKind Op;

public:
  ASTUnaryOperatorExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Operand,
                       ASTUnaryOperatorKind Op)
      : ASTNode(ASTNodeKind::UnaryOperatorExpr, Loc),
        Operand(std::move(Operand)), Op(Op) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::UnaryOperatorExpr;
  }
};

class ASTConstantIndexExpr : public ASTNode {
  std::unique_ptr<ASTNode> Source;
  std::unique_ptr<Identifier> Index;

public:
  ASTConstantIndexExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Source,
                       std::unique_ptr<Identifier> Index)
      : ASTNode(ASTNodeKind::ConstantIndexExpr, Loc), Source(std::move(Source)),
        Index(std::move(Index)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ConstantIndexExpr;
  }
};

class ASTVariableIndexExpr : public ASTNode {
  std::unique_ptr<ASTNode> Source;
  std::unique_ptr<ASTNode> Index;

public:
  ASTVariableIndexExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Source,
                       std::unique_ptr<ASTNode> Index)
      : ASTNode(ASTNodeKind::VariableIndexExpr, Loc), Source(std::move(Source)),
        Index(std::move(Index)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::VariableIndexExpr;
  }
};

class ASTReferenceExpr : public ASTNode {
  std::unique_ptr<Identifier> Name;

public:
  ASTReferenceExpr(SourceLocation Loc, std::unique_ptr<Identifier> Name)
      : ASTNode(ASTNodeKind::ReferenceExpr, Loc), Name(std::move(Name)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ReferenceExpr;
  }
};

class ASTCallExpr : public ASTNode {
  std::unique_ptr<ASTNode> Callable;
  std::vector<std::unique_ptr<ASTNode>> Arguments;

public:
  ASTCallExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Callable,
              std::vector<std::unique_ptr<ASTNode>>)
      : ASTNode(ASTNodeKind::CallExpr, Loc), Callable(std::move(Callable)),
        Arguments(std::move(Arguments)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::CallExpr;
  }
};

class ASTConstructionExpr : public ASTNode {
public:
  class ConstructionArgument {
    SourceLocation Loc;
    std::unique_ptr<Identifier> Name;
    std::unique_ptr<ASTNode> Value;

  public:
    ConstructionArgument(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                         std::unique_ptr<ASTNode> Value)
        : Loc(Loc), Name(std::move(Name)), Value(std::move(Value)) {}
  };

private:
  // TODO: Replace with typename
  std::unique_ptr<ASTNode> Constructor;
  std::vector<std::unique_ptr<ConstructionArgument>> Arguments;

public:
  ASTConstructionExpr(
      SourceLocation Loc, std::unique_ptr<ASTNode> Constructor,
      std::vector<std::unique_ptr<ConstructionArgument>> Arguments)
      : ASTNode(ASTNodeKind::ConstructionExpr, Loc),
        Constructor(std::move(Constructor)), Arguments(std::move(Arguments)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ConstructionExpr;
  }
};

class ASTGroupingExpr : public ASTNode {
  std::unique_ptr<ASTNode> Expr;

public:
  ASTGroupingExpr(SourceLocation Loc, std::unique_ptr<ASTNode> Expr)
      : ASTNode(ASTNodeKind::GroupingExpr, Loc), Expr(std::move(Expr)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::GroupingExpr;
  }
};

} // namespace xd

#endif // AST_H
