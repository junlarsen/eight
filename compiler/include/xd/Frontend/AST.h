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
#include <memory>
#include <vector>

namespace xd {
class ASTItem;
class ASTFunctionItem;
class ASTTypeItem;
class ASTStructItem;
class ASTTraitItem;
class ASTInstanceItem;

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
  Item,
  FunctionItem,
  TypeItem,
  StructItem,
  TraitItem,
  InstanceItem,

  Stmt,
  LetStmt,
  ReturnStmt,
  ForStmt,
  BreakStmt,
  ContinueStmt,
  IfStmt,
  ExprStmt,

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
  auto getKind() const -> ASTNodeKind { return Kind; }
  auto getLoc() const -> SourceLocation { return Loc; }
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
  std::vector<std::unique_ptr<ASTType>> TypeArguments;

public:
  ASTCallExpr(SourceLocation Loc, std::unique_ptr<ASTExpr> Callable,
              std::vector<std::unique_ptr<ASTExpr>> Arguments,
              std::vector<std::unique_ptr<ASTType>> TypeArguments)
      : ASTExpr(ASTNodeKind::CallExpr, Loc), Callable(std::move(Callable)),
        Arguments(std::move(Arguments)),
        TypeArguments(std::move(TypeArguments)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::CallExpr;
  }
};

/// Represents a single key-value pair given to a construction expression.
///
/// This class does have a classof, as it's a pure data class and not part of
/// the AST hierarchy.
class ASTConstructionArgument {
  SourceLocation Loc;
  std::unique_ptr<Identifier> Name;
  std::unique_ptr<ASTExpr> Value;

public:
  ASTConstructionArgument(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                          std::unique_ptr<ASTExpr> Value)
      : Loc(Loc), Name(std::move(Name)), Value(std::move(Value)) {}
};

class ASTConstructionExpr : public ASTExpr {
  std::unique_ptr<ASTType> Constructor;
  std::vector<std::unique_ptr<ASTConstructionArgument>> Arguments;

public:
  ASTConstructionExpr(
      SourceLocation Loc, std::unique_ptr<ASTType> Constructor,
      std::vector<std::unique_ptr<ASTConstructionArgument>> Arguments)
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

class ASTStmt : public ASTNode {
public:
  ASTStmt(ASTNodeKind Kind, SourceLocation Loc) : ASTNode(Kind, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() >= ASTNodeKind::Stmt &&
           Node->getKind() <= ASTNodeKind::ExprStmt;
  }
};

class ASTLetStmt : public ASTStmt {
  std::unique_ptr<Identifier> Name;
  std::unique_ptr<ASTExpr> Value;
  std::optional<std::unique_ptr<ASTType>> TypeAnnotation;

public:
  ASTLetStmt(SourceLocation Loc, std::unique_ptr<Identifier> Name,
             std::unique_ptr<ASTExpr> Value,
             std::optional<std::unique_ptr<ASTType>> TypeAnnotation)
      : ASTStmt(ASTNodeKind::LetStmt, Loc), Name(std::move(Name)),
        Value(std::move(Value)), TypeAnnotation(std::move(TypeAnnotation)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::LetStmt;
  }
};

class ASTReturnStmt : public ASTStmt {
  std::optional<std::unique_ptr<ASTExpr>> Value;

public:
  ASTReturnStmt(SourceLocation Loc, std::unique_ptr<ASTExpr> Value)
      : ASTStmt(ASTNodeKind::ReturnStmt, Loc), Value(std::move(Value)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ReturnStmt;
  }
};

class ASTForStmt : public ASTStmt {
  std::optional<std::unique_ptr<ASTExpr>> Init;
  std::unique_ptr<ASTExpr> Condition;
  std::optional<std::unique_ptr<ASTExpr>> Increment;
  std::vector<std::unique_ptr<ASTStmt>> Body;

public:
  ASTForStmt(SourceLocation Loc, std::unique_ptr<ASTExpr> Init,
             std::unique_ptr<ASTExpr> Condition,
             std::optional<std::unique_ptr<ASTExpr>> Increment,
             std::vector<std::unique_ptr<ASTStmt>> Body)
      : ASTStmt(ASTNodeKind::ForStmt, Loc), Init(std::move(Init)),
        Condition(std::move(Condition)), Increment(std::move(Increment)),
        Body(std::move(Body)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ForStmt;
  }
};

class ASTBreakStmt : public ASTStmt {
public:
  ASTBreakStmt(SourceLocation Loc) : ASTStmt(ASTNodeKind::BreakStmt, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::BreakStmt;
  }
};

class ASTContinueStmt : public ASTStmt {
public:
  ASTContinueStmt(SourceLocation Loc)
      : ASTStmt(ASTNodeKind::ContinueStmt, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ContinueStmt;
  }
};

class ASTIfStmt : public ASTStmt {
  std::unique_ptr<ASTExpr> Condition;
  std::vector<std::unique_ptr<ASTStmt>> Then;
  std::optional<std::vector<std::unique_ptr<ASTExpr>>> Else;

public:
  ASTIfStmt(SourceLocation Loc, std::unique_ptr<ASTExpr> Condition,
            std::vector<std::unique_ptr<ASTStmt>> Then,
            std::optional<std::vector<std::unique_ptr<ASTExpr>>> Else)
      : ASTStmt(ASTNodeKind::IfStmt, Loc), Condition(std::move(Condition)),
        Then(std::move(Then)), Else(std::move(Else)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::IfStmt;
  }
};

class ASTExprStmt : public ASTStmt {
  std::unique_ptr<ASTExpr> Value;

public:
  ASTExprStmt(SourceLocation Loc, std::unique_ptr<ASTExpr> Value)
      : ASTStmt(ASTNodeKind::ExprStmt, Loc), Value(std::move(Value)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::ExprStmt;
  }
};

class ASTItem : public ASTNode {
public:
  ASTItem(ASTNodeKind Kind, SourceLocation Loc) : ASTNode(Kind, Loc) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() >= ASTNodeKind::Item &&
           Node->getKind() <= ASTNodeKind::InstanceItem;
  }
};

/// Represents a single type parameter in a list such as <T, K>.
///
/// This class does have a classof, as it's a pure data class and not part of
/// the AST hierarchy.
class ASTTypeParameter {
  SourceLocation Loc;
  std::unique_ptr<Identifier> Name;

public:
  ASTTypeParameter(SourceLocation Loc, std::unique_ptr<Identifier> Name)
      : Loc(Loc), Name(std::move(Name)) {}
};

/// Represents a single function parameter on a function.
///
/// This class does have a classof, as it's a pure data class and not part of
/// the AST hierarchy.
class ASTFunctionParameter {
  SourceLocation Loc;
  std::unique_ptr<Identifier> Name;
  std::unique_ptr<ASTType> TypeAnnotation;

public:
  ASTFunctionParameter(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                       std::unique_ptr<ASTType> TypeAnnotation)
      : Loc(Loc), Name(std::move(Name)),
        TypeAnnotation(std::move(TypeAnnotation)) {}
};

class ASTFunctionItem : public ASTItem {
  std::unique_ptr<Identifier> Name;
  std::vector<std::unique_ptr<ASTTypeParameter>> TypeParameters;
  std::vector<std::unique_ptr<ASTFunctionParameter>> Parameters;
  std::optional<std::unique_ptr<ASTType>> ReturnTypeAnnotation;
  std::vector<std::unique_ptr<ASTStmt>> Body;

  /// Is the function marked as intrinsic to the compiler? In other words, does
  /// it not have a body, and did it come from an intrinsic_fn declaration?
  bool IsIntrinsic;

public:
  ASTFunctionItem(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                  std::vector<std::unique_ptr<ASTTypeParameter>> TypeParameters,
                  std::vector<std::unique_ptr<ASTFunctionParameter>> Parameters,
                  std::optional<std::unique_ptr<ASTType>> ReturnTypeAnnotation,
                  bool IsIntrinsic)
      : ASTItem(ASTNodeKind::FunctionItem, Loc), Name(std::move(Name)),
        TypeParameters(std::move(TypeParameters)),
        Parameters(std::move(Parameters)),
        ReturnTypeAnnotation(std::move(ReturnTypeAnnotation)),
        IsIntrinsic(IsIntrinsic) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::FunctionItem;
  }
};

/// Represents an intrinsic scalar type, such as i32.
///
/// We provide these in the standard library and type them out so that the LSP
/// can have goto-definitions for them, as well as documentation on the types
/// themselves.
class ASTTypeItem : public ASTItem {
  std::unique_ptr<Identifier> Name;

public:
  ASTTypeItem(SourceLocation Loc, std::unique_ptr<Identifier> Name)
      : ASTItem(ASTNodeKind::TypeItem, Loc), Name(std::move(Name)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::TypeItem;
  }
};

/// Represents a single name and type pair of a struct definition.
///
/// This class does have a classof, as it's a pure data class and not part of
/// the AST hierarchy.
class ASTStructMember {
  SourceLocation Loc;
  std::unique_ptr<Identifier> Name;
  std::unique_ptr<ASTType> TypeAnnotation;

public:
  ASTStructMember(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                  std::unique_ptr<ASTType> TypeAnnotation)
      : Loc(Loc), Name(std::move(Name)),
        TypeAnnotation(std::move(TypeAnnotation)) {}
};

class ASTStructItem : public ASTItem {
  std::unique_ptr<Identifier> Name;
  std::vector<std::unique_ptr<ASTStructMember>> Members;

public:
  ASTStructItem(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                std::vector<std::unique_ptr<ASTStructMember>> Members)
      : ASTItem(ASTNodeKind::StructItem, Loc), Name(std::move(Name)),
        Members(std::move(Members)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::StructItem;
  }
};

/// Represent a trait member declaration.
///
/// This class does have a classof, as it's a pure data class and not part of
/// the AST hierarchy.
class ASTTraitFunction {
  SourceLocation Loc;
  std::unique_ptr<Identifier> Name;
  std::vector<std::unique_ptr<ASTType>> TypeParameters;
  std::vector<std::unique_ptr<ASTFunctionParameter>> Parameters;
  std::optional<std::unique_ptr<ASTType>> ReturnTypeAnnotation;

  /// Is the trait member definition intrinsic?
  ///
  /// Traits such as Add have intrinsic implementations for simple types like
  /// i32.
  bool IsIntrinsic;

public:
  ASTTraitFunction(
      SourceLocation Loc, std::unique_ptr<Identifier> Name,
      std::vector<std::unique_ptr<ASTType>> TypeParameters,
      std::vector<std::unique_ptr<ASTFunctionParameter>> Parameters,
      std::optional<std::unique_ptr<ASTType>> ReturnTypeAnnotation,
      bool IsIntrinsic)
      : Loc(Loc), Name(std::move(Name)),
        TypeParameters(std::move(TypeParameters)),
        Parameters(std::move(Parameters)),
        ReturnTypeAnnotation(std::move(ReturnTypeAnnotation)),
        IsIntrinsic(IsIntrinsic) {}
};

class ASTTraitItem : public ASTItem {
  std::unique_ptr<Identifier> Name;
  std::vector<std::unique_ptr<ASTType>> TypeParameters;
  std::vector<std::unique_ptr<ASTTraitFunction>> FunctionMembers;

public:
  ASTTraitItem(SourceLocation Loc, std::unique_ptr<Identifier> Name,
               std::vector<std::unique_ptr<ASTType>> TypeParameters,
               std::vector<std::unique_ptr<ASTTraitFunction>> FunctionMembers)
      : ASTItem(ASTNodeKind::TraitItem, Loc), Name(std::move(Name)),
        TypeParameters(std::move(TypeParameters)),
        FunctionMembers(std::move(FunctionMembers)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::TraitItem;
  }
};

class ASTInstanceItem : public ASTItem {
  std::unique_ptr<Identifier> Name;
  std::vector<std::unique_ptr<ASTType>> TypeArguments;
  std::vector<std::unique_ptr<ASTFunctionItem>> FunctionMembers;

public:
  ASTInstanceItem(SourceLocation Loc, std::unique_ptr<Identifier> Name,
                  std::vector<std::unique_ptr<ASTType>> TypeArguments,
                  std::vector<std::unique_ptr<ASTFunctionItem>> FunctionMembers)
      : ASTItem(ASTNodeKind::InstanceItem, Loc), Name(std::move(Name)),
        TypeArguments(std::move(TypeArguments)),
        FunctionMembers(std::move(FunctionMembers)) {}
  static bool classof(const ASTNode *Node) {
    return Node->getKind() == ASTNodeKind::InstanceItem;
  }
};

} // namespace xd

#endif // XD_FRONTEND_AST_H
