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
class ASTUnitType;
class ASTIntegerType;
class ASTBooleanType;
class ASTPointerType;
class ASTOpaquePointerType;
class ASTNamedType;

class Identifier {
  std::string Name;
  SourceLocation Loc;

public:
  Identifier(std::string Name, SourceLocation Loc) : Name(Name), Loc(Loc) {}
  std::string getName() const { return Name; }
  SourceLocation getLoc() const { return Loc; }
};

enum class ASTNodeKind {
  Expr,
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

  Type,
  UnitType,
  IntegerType,
  BooleanType,
  PointerType,
  OpaquePointerType,
  NamedType,
};

class ASTNode {
  const ASTNodeKind Kind;
  SourceLocation Loc;

public:
  ASTNode(ASTNodeKind Kind, SourceLocation Loc) : Kind(Kind), Loc(Loc) {}
  ASTNodeKind getKind() const { return Kind; }
  SourceLocation getLoc() const { return Loc; }
};

class ASTExpr : public ASTNode {
public:
  ASTExpr(ASTNodeKind Kind, SourceLocation Loc) : ASTNode(Kind, Loc) {}
  static bool classof(ASTNode *Node) {
    return Node->getKind() >= ASTNodeKind::Expr &&
           Node->getKind() <= ASTNodeKind::GroupingExpr;
  }
};

class ASTIntegerLiteralExpr : public ASTExpr {
  llvm::APInt Value;

public:
  ASTIntegerLiteralExpr(SourceLocation Loc, llvm::APInt Value)
      : ASTExpr(ASTNodeKind::IntegerLiteralExpr, Loc), Value(Value) {}

  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::IntegerLiteralExpr;
  }
};

class ASTBooleanLiteralExpr : public ASTExpr {
  llvm::APInt Value;

public:
  ASTBooleanLiteralExpr(SourceLocation Loc, llvm::APInt Value)
      : ASTExpr(ASTNodeKind::BooleanLiteralExpr, Loc), Value(Value) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::BooleanLiteralExpr;
  }
};

class ASTAssignmentExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> Destination;
  std::unique_ptr<ASTExpr> Value;

public:
  ASTAssignmentExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Destination,
                    std::unique_ptr<ASTExpr> Value)
      : ASTExpr(ASTNodeKind::AssignmentExpr, Loc),
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

class ASTBinaryOperatorExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> LHS;
  std::unique_ptr<ASTExpr> RHS;
  ASTBinaryOperatorKind Op;

public:
  ASTBinaryOperatorExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> LHS,
                        ASTBinaryOperatorKind Op)
      : ASTExpr(ASTNodeKind::BinaryOperatorExpr, Loc), LHS(std::move(LHS)),
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

class ASTUnaryOperatorExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> Operand;
  ASTUnaryOperatorKind Op;

public:
  ASTUnaryOperatorExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Operand,
                       ASTUnaryOperatorKind Op)
      : ASTExpr(ASTNodeKind::UnaryOperatorExpr, Loc),
        Operand(std::move(Operand)), Op(Op) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::UnaryOperatorExpr;
  }
};

class ASTConstantIndexExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> Source;
  std::unique_ptr<Identifier> Index;

public:
  ASTConstantIndexExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Source,
                       std::unique_ptr<Identifier> Index)
      : ASTExpr(ASTNodeKind::ConstantIndexExpr, Loc), Source(std::move(Source)),
        Index(std::move(Index)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ConstantIndexExpr;
  }
};

class ASTVariableIndexExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> Source;
  std::unique_ptr<ASTExpr> Index;

public:
  ASTVariableIndexExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Source,
                       std::unique_ptr<ASTExpr> Index)
      : ASTExpr(ASTNodeKind::VariableIndexExpr, Loc), Source(std::move(Source)),
        Index(std::move(Index)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::VariableIndexExpr;
  }
};

class ASTReferenceExpr : public ASTExpr {
  std::unique_ptr<Identifier> Name;

public:
  ASTReferenceExpr(SourceLocation Loc, std::unique_ptr<Identifier> Name)
      : ASTExpr(ASTNodeKind::ReferenceExpr, Loc), Name(std::move(Name)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ReferenceExpr;
  }
};

class ASTCallExpr : public ASTExpr {
  std::unique_ptr<ASTExpr> Callable;
  std::vector<std::unique_ptr<ASTExpr>> Arguments;

public:
  ASTCallExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Callable,
              std::vector<std::unique_ptr<ASTExpr>>)
      : ASTExpr(ASTNodeKind::CallExpr, Loc), Callable(std::move(Callable)),
        Arguments(std::move(Arguments)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::CallExpr;
  }
};

class ASTConstructionExpr : public ASTExpr {
public:
  class ConstructionArgument {
    SourceLocation Loc;
    std::unique_ptr<Identifier> Name;
    std::unique_ptr<ASTExpr> Value;

  public:
    ConstructionArgument(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                         std::unique_ptr<ASTExpr> Value)
        : Loc(Loc), Name(std::move(Name)), Value(std::move(Value)) {}
  };

private:
  std::unique_ptr<ASTType> Constructor;
  std::vector<std::unique_ptr<ConstructionArgument>> Arguments;

public:
  ASTConstructionExpr(
      SourceLocation Loc, std::unique_ptr<ASTType> Constructor,
      std::vector<std::unique_ptr<ConstructionArgument>> Arguments)
      : ASTExpr(ASTNodeKind::ConstructionExpr, Loc),
        Constructor(std::move(Constructor)), Arguments(std::move(Arguments)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ConstructionExpr;
  }
};

class ASTGroupingExpr : public ASTExpr {
  std::unique_ptr<ASTNode> Expr;

public:
  ASTGroupingExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Expr)
      : ASTExpr(ASTNodeKind::GroupingExpr, Loc), Expr(std::move(Expr)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::GroupingExpr;
  }
};

class ASTType : public ASTNode {
public:
  ASTType(ASTNodeKind Kind, SourceLocation Loc) : ASTNode(Kind, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() >= ASTNodeKind::Type &&
           Node->getKind() <= ASTNodeKind::NamedType;
  }
};

class ASTUnitType : public ASTType {
public:
  ASTUnitType(SourceLocation Loc) : ASTType(ASTNodeKind::UnitType, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::UnitType;
  }
};

class ASTIntegerType : public ASTType {
  uint32_t Width;

public:
  ASTIntegerType(SourceLocation Loc, uint32_t Width)
      : ASTType(ASTNodeKind::IntegerType, Loc), Width(Width) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::IntegerType;
  }
};

class ASTBooleanType : public ASTType {
public:
  ASTBooleanType(SourceLocation Loc) : ASTType(ASTNodeKind::BooleanType, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::BooleanType;
  }
};

class ASTPointerType : public ASTType {
  std::unique_ptr<ASTType> Inner;

public:
  ASTPointerType(SourceLocation Loc, std::unique_ptr<ASTType> Inner)
      : ASTType(ASTNodeKind::PointerType, Loc), Inner(std::move(Inner)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::PointerType;
  }
};

class ASTOpaquePointerType : public ASTType {
public:
  ASTOpaquePointerType(SourceLocation Loc, std::unique_ptr<ASTType> Inner)
      : ASTType(ASTNodeKind::OpaquePointerType, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::OpaquePointerType;
  }
};

class ASTNamedType : public ASTType {
  std::unique_ptr<Identifier> Name;

public:
  ASTNamedType(SourceLocation Loc, std::unique_ptr<Identifier> Name)
      : ASTType(ASTNodeKind::NamedType, Loc), Name(std::move(Name)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::NamedType;
  }
};

} // namespace xd

#endif // AST_H
