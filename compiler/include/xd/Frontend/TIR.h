//===----- TIR.h - Typed intermediate representation ----------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Typed intermediate representation (TIR) is a desugared, simplified
// representation of the source code. It's the representation that type checking
// and inference is performed on.
//
// TIR starts off untyped before it's type checked. After the type-checker pass
// the entire TIR tree is guaranteed to be well-typed. If there were zero error
// diagnostics emitted after this phase, the TIR is also guaranteed to be valid.
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_TIR_H
#define XD_FRONTEND_TIR_H

#include "xd/Basic/Location.h"
#include "llvm/ADT/APInt.h"
#include <memory>

namespace xd {
/// The different types of TIR nodes.
///
/// This enum holds the documentation for a lot of the TIR structure, so it's
/// useful to read through first.
///
/// 1. Import declarations are not modelled in TIR, they are instead verified
///    before TIR lowering. This is because import resolution is a rather easy
///    process (simply check if the given module has said symbol). We can't say
///    anything about the correctness of the type before type checking anyway,
///    so there is no point in modelling them here. This reduces both the size
///    and complexity of the TIR tree.
///
/// 2. The TIR does simplifications and rewrites of the AST. For example, the
///    grouping expressions are eliminated, and for loops are rewritten into
///    infinite loops with if statements.
///
/// 3. Because string literals are not in the language yet, and only show up in
///    import paths, they do not have a node.
///
/// 4.The unary operators for address-of and dereference are turned into their
///   own node types. The rest of the unary and binary operators are rewritten
///   into call expressions onto the respective built-in traits.
enum class TIRNodeKind : uint8_t {
  Name,
  // Declaration nodes
  Decl,
  /// The module declaration node.
  ///
  /// It corresponds to a single AST translation unit. The entire AST
  /// translation unit is effectively flattened into a single TIR module.
  ModuleDecl,
  FunctionDecl,
  TypeDecl,
  StructDecl,
  TraitDecl,
  InstanceDecl,

  // Statement nodes
  Stmt,
  LoopStmt,
  IfStmt,
  ReturnStmt,
  ContinueStmt,
  BreakStmt,
  ExprStmt,

  // Expression nodes
  Expr,
  IntLitExpr,
  BoolLitExpr,
  ReferenceExpr,
  ConstantIndexExpr,
  CallExpr,
  AddrOfExpr,
  DerefExpr,
  ConstructionExpr,

  // Type nodes
  Type,
  /// Another named type, typically a struct or a trait.
  NamedType,
  /// A pointer to another type.
  PointerType,
  Integer32Type,
  BooleanType,
  /// The empty type, which is used to represent no return value.
  VoidType,
  /// The special-cased `Self` type available for trait methods.
  SelfType,
  /// A type variable to be instantiated during type checking.
  ///
  /// Indexed using de Bruijn indices of (depth, index) pairs. This is used to
  /// track nested type variables in places such as traits and trait methods.
  VariableType,
  /// A unification meta variable.
  MetaType,
  /// A function type with a list of parameters and a return type. The type
  /// parameters of the function are stored as `VariableType` nodes in the
  /// parameters list.
  FunctionType,
  /// The type is not yet known, and must be inferred during type checking.
  UnknownType,
  /// An error type, which is used to prevent further propagation of constraints
  /// in the unification algorithm when a type cannot be deduced.
  ///
  /// This is useful because we perform type-checking on partial syntax trees
  /// that may contain syntax errors. If we encounter something that's missing
  /// we give it TheHole, which cannot be unified with anything else.
  ErrorType,
};

class TIRNode {
  TIRNodeKind Kind;

  /// The source location in the source code corresponding to this node.
  ///
  /// For most transforms we will be able to preserve the source location in the
  /// syntax tree. This enables us to give good diagnostics to the user.
  SourceLocation Loc;

public:
  explicit TIRNode(TIRNodeKind Kind, SourceLocation Loc)
      : Kind(Kind), Loc(Loc) {}
  auto getKind() const -> TIRNodeKind { return Kind; }
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Name &&
           N->getKind() <= TIRNodeKind::ErrorType;
  }

  auto getLocation() const -> SourceLocation { return Loc; }
};

/// A name that was written by the programmer.
///
/// This effectively corresponds to the identifier in the AST.
class TIRName : public TIRNode {
  std::string Name;

public:
  explicit TIRName(std::string Name, SourceLocation Loc)
      : TIRNode(TIRNodeKind::Name, Loc), Name(std::move(Name)) {}
  auto getName() const -> const std::string & { return Name; }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::Name;
  }
};

class TIRType : public TIRNode {
public:
  explicit TIRType(TIRNodeKind Kind, SourceLocation Loc) : TIRNode(Kind, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Type &&
           N->getKind() <= TIRNodeKind::ErrorType;
  }
};

class TIRNamedType : public TIRType {
  std::unique_ptr<TIRName> Name;

public:
  explicit TIRNamedType(std::unique_ptr<TIRName> Name, SourceLocation Loc)
      : TIRType(TIRNodeKind::NamedType, Loc), Name(std::move(Name)) {}
  auto getName() const -> const TIRName & { return *Name; }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::NamedType;
  }
};

class TIRPointerType : public TIRType {
  std::unique_ptr<TIRType> Inner;

public:
  explicit TIRPointerType(std::unique_ptr<TIRType> Inner, SourceLocation Loc)
      : TIRType(TIRNodeKind::PointerType, Loc), Inner(std::move(Inner)) {}
  auto getInnerType() const -> const TIRType & { return *Inner; }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::PointerType;
  }
};

class TIRInteger32Type : public TIRType {
public:
  explicit TIRInteger32Type(SourceLocation Loc)
      : TIRType(TIRNodeKind::Integer32Type, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::Integer32Type;
  }
};

class TIRBooleanType : public TIRType {
public:
  explicit TIRBooleanType(SourceLocation Loc)
      : TIRType(TIRNodeKind::BooleanType, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::BooleanType;
  }
};

class TIRVoidType : public TIRType {
public:
  explicit TIRVoidType(SourceLocation Loc)
      : TIRType(TIRNodeKind::VoidType, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::VoidType;
  }
};

class TIRSelfType : public TIRType {
public:
  explicit TIRSelfType(SourceLocation Loc)
      : TIRType(TIRNodeKind::SelfType, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::SelfType;
  }
};

class TIRVariableType : public TIRType {
  int32_t Depth;
  int32_t Index;

public:
  explicit TIRVariableType(int32_t Depth, int32_t Index, SourceLocation Loc)
      : TIRType(TIRNodeKind::VariableType, Loc), Depth(Depth), Index(Index) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::VariableType;
  }

  auto getDepth() const -> int32_t { return Depth; }
  auto getIndex() const -> int32_t { return Index; }
};

class TIRMetaVariableType : public TIRType {
  int32_t ID;

public:
  explicit TIRMetaVariableType(int32_t ID, SourceLocation Loc)
      : TIRType(TIRNodeKind::MetaType, Loc), ID(ID) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::MetaType;
  }

  auto getID() const -> int32_t { return ID; }
};

class TIRFunctionType : public TIRType {
  std::vector<std::unique_ptr<TIRType>> Parameters;
  std::unique_ptr<TIRType> ReturnType;

public:
  explicit TIRFunctionType(std::vector<std::unique_ptr<TIRType>> Parameters,
                           std::unique_ptr<TIRType> ReturnType,
                           SourceLocation Loc)
      : TIRType(TIRNodeKind::FunctionType, Loc),
        Parameters(std::move(Parameters)), ReturnType(std::move(ReturnType)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::FunctionType;
  }

  auto getParameters() const -> const std::vector<std::unique_ptr<TIRType>> & {
    return Parameters;
  }
  auto getReturnType() const -> const TIRType & { return *ReturnType; }
};

class TIRUnknownType : public TIRType {
public:
  explicit TIRUnknownType(SourceLocation Loc)
      : TIRType(TIRNodeKind::UnknownType, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::UnknownType;
  }
};

class TIRErrorType : public TIRType {
public:
  explicit TIRErrorType(SourceLocation Loc)
      : TIRType(TIRNodeKind::ErrorType, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ErrorType;
  }
};

/// Represents any expression node in the TIR.
///
/// All expressions are of some type, so the type is stored on this class.
class TIRExpr : public TIRNode {
  std::unique_ptr<TIRType> Type;

public:
  explicit TIRExpr(TIRNodeKind Kind, SourceLocation Loc,
                   std::unique_ptr<TIRType> Type)
      : TIRNode(Kind, Loc), Type(std::move(Type)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Expr &&
           N->getKind() <= TIRNodeKind::ConstructionExpr;
  }

  /// Get the type of this expression node.
  auto getType() const -> const TIRType & { return *Type; }
};

class TIRIntLitExpr : public TIRExpr {
  llvm::APInt Value;

public:
  explicit TIRIntLitExpr(llvm::APInt Value, SourceLocation Loc,
                         std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::IntLitExpr, Loc, std::move(Type)), Value(Value) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::IntLitExpr;
  }

  auto getValue() const -> const llvm::APInt & { return Value; }
};

class TIRBoolLitExpr : public TIRExpr {
  bool Value;

public:
  explicit TIRBoolLitExpr(bool Value, SourceLocation Loc,
                          std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::BoolLitExpr, Loc, std::move(Type)), Value(Value) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::BoolLitExpr;
  }

  auto getValue() const -> bool { return Value; }
};

class TIRReferenceExpr : public TIRExpr {
  std::unique_ptr<TIRName> Name;

public:
  explicit TIRReferenceExpr(std::unique_ptr<TIRName> Name, SourceLocation Loc,
                            std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::ReferenceExpr, Loc, std::move(Type)),
        Name(std::move(Name)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ReferenceExpr;
  }

  auto getName() const -> const TIRName & { return *Name; }
};

class TIRConstantIndexExpr : public TIRExpr {
  std::unique_ptr<TIRName> Index;

public:
  explicit TIRConstantIndexExpr(std::unique_ptr<TIRName> Index,
                                SourceLocation Loc,
                                std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::ConstantIndexExpr, Loc, std::move(Type)),
        Index(std::move(Index)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ConstantIndexExpr;
  }

  auto getIndex() const -> const TIRName & { return *Index; }
};

class TIRCallExpr : public TIRExpr {
  std::unique_ptr<TIRExpr> Callee;
  std::vector<std::unique_ptr<TIRExpr>> Arguments;
  std::vector<std::unique_ptr<TIRType>> TypeArguments;

public:
  explicit TIRCallExpr(std::unique_ptr<TIRExpr> Callee,
                       std::vector<std::unique_ptr<TIRExpr>> Arguments,
                       std::vector<std::unique_ptr<TIRType>> TypeArguments,
                       SourceLocation Loc, std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::CallExpr, Loc, std::move(Type)),
        Callee(std::move(Callee)), Arguments(std::move(Arguments)),
        TypeArguments(std::move(TypeArguments)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::CallExpr;
  }

  auto getCallee() const -> const TIRExpr & { return *Callee; }
  auto getArguments() const -> const std::vector<std::unique_ptr<TIRExpr>> & {
    return Arguments;
  }
  auto getTypeArguments() const
      -> const std::vector<std::unique_ptr<TIRType>> & {
    return TypeArguments;
  }
};

class TIRAddrOfExpr : public TIRExpr {
  std::unique_ptr<TIRExpr> Inner;

public:
  explicit TIRAddrOfExpr(std::unique_ptr<TIRExpr> Inner, SourceLocation Loc,
                         std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::AddrOfExpr, Loc, std::move(Type)),
        Inner(std::move(Inner)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::AddrOfExpr;
  }

  auto getInner() const -> const TIRExpr & { return *Inner; }
};

class TIRDerefExpr : public TIRExpr {
  std::unique_ptr<TIRExpr> Inner;

public:
  explicit TIRDerefExpr(std::unique_ptr<TIRExpr> Inner, SourceLocation Loc,
                        std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::DerefExpr, Loc, std::move(Type)),
        Inner(std::move(Inner)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::DerefExpr;
  }

  auto getInner() const -> const TIRExpr & { return *Inner; }
};

class TIRConstructionExpr : public TIRExpr {
public:
  class Member : public TIRNode {
    std::unique_ptr<TIRName> Name;
    std::unique_ptr<TIRExpr> Value;

  public:
    explicit Member(std::unique_ptr<TIRName> Name,
                    std::unique_ptr<TIRExpr> Value, SourceLocation Loc)
        : TIRNode(TIRNodeKind::Name, Loc), Name(std::move(Name)),
          Value(std::move(Value)) {}
    static bool classof(const TIRNode *N) { return false; }

    auto getName() const -> const TIRName & { return *Name; }
    auto getValue() const -> const TIRExpr & { return *Value; }
  };

protected:
  std::unique_ptr<TIRName> Constructor;
  std::vector<std::unique_ptr<Member>> Members;

public:
  explicit TIRConstructionExpr(std::unique_ptr<TIRName> Constructor,
                               std::vector<std::unique_ptr<Member>> Members,
                               SourceLocation Loc,
                               std::unique_ptr<TIRType> Type)
      : TIRExpr(TIRNodeKind::ConstructionExpr, Loc, std::move(Type)),
        Constructor(std::move(Constructor)), Members(std::move(Members)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ConstructionExpr;
  }

  auto getConstructor() const -> const TIRName & { return *Constructor; }
  auto getArguments() const -> const std::vector<std::unique_ptr<Member>> & {
    return Members;
  }
};

class TIRStmt : public TIRNode {
public:
  explicit TIRStmt(TIRNodeKind Kind, SourceLocation Loc) : TIRNode(Kind, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Stmt &&
           N->getKind() <= TIRNodeKind::ExprStmt;
  }
};

class TIRLoopStmt : public TIRStmt {
  std::vector<std::unique_ptr<TIRStmt>> Statements;

public:
  explicit TIRLoopStmt(std::vector<std::unique_ptr<TIRStmt>> Statements,
                       SourceLocation Loc)
      : TIRStmt(TIRNodeKind::LoopStmt, Loc), Statements(std::move(Statements)) {
  }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::LoopStmt;
  }

  auto getStatements() const -> const std::vector<std::unique_ptr<TIRStmt>> & {
    return Statements;
  }
};

class TIRIfStmt : public TIRStmt {
  std::unique_ptr<TIRExpr> Condition;
  std::vector<std::unique_ptr<TIRStmt>> ThenStatements;
  std::vector<std::unique_ptr<TIRStmt>> ElseStatements;

public:
  explicit TIRIfStmt(std::unique_ptr<TIRExpr> Condition,
                     std::vector<std::unique_ptr<TIRStmt>> ThenStatements,
                     std::vector<std::unique_ptr<TIRStmt>> ElseStatements,
                     SourceLocation Loc)
      : TIRStmt(TIRNodeKind::IfStmt, Loc), Condition(std::move(Condition)),
        ThenStatements(std::move(ThenStatements)),
        ElseStatements(std::move(ElseStatements)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::IfStmt;
  }

  auto getCondition() const -> const TIRExpr & { return *Condition; }
  auto getThenStatements() const
      -> const std::vector<std::unique_ptr<TIRStmt>> & {
    return ThenStatements;
  }
  auto getElseStatements() const
      -> const std::vector<std::unique_ptr<TIRStmt>> & {
    return ElseStatements;
  }
};

class TIRReturnStmt : public TIRStmt {
  std::optional<std::unique_ptr<TIRExpr>> ReturnValue;

public:
  explicit TIRReturnStmt(std::optional<std::unique_ptr<TIRExpr>> ReturnValue,
                         SourceLocation Loc)
      : TIRStmt(TIRNodeKind::ReturnStmt, Loc),
        ReturnValue(std::move(ReturnValue)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ReturnStmt;
  }
  auto getReturnValue() const -> std::optional<TIRExpr &> {
    return **ReturnValue;
  }
};

class TIRContinueStmt : public TIRStmt {
public:
  explicit TIRContinueStmt(SourceLocation Loc)
      : TIRStmt(TIRNodeKind::ContinueStmt, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ContinueStmt;
  }
};

class TIRBreakStmt : public TIRStmt {
public:
  explicit TIRBreakStmt(SourceLocation Loc)
      : TIRStmt(TIRNodeKind::BreakStmt, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::BreakStmt;
  }
};

class TIRExprStmt : public TIRStmt {
  std::unique_ptr<TIRExpr> Expression;

public:
  explicit TIRExprStmt(std::unique_ptr<TIRExpr> Expression, SourceLocation Loc)
      : TIRStmt(TIRNodeKind::ExprStmt, Loc), Expression(std::move(Expression)) {
  }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::ExprStmt;
  }
};

class TIRDecl : public TIRNode {
public:
  explicit TIRDecl(TIRNodeKind Kind, SourceLocation Loc) : TIRNode(Kind, Loc) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Decl &&
           N->getKind() <= TIRNodeKind::InstanceDecl;
  }
};

class TIRFunctionDecl : public TIRDecl {
public:
  class Parameter : public TIRNode {
    std::unique_ptr<TIRName> Name;
    std::unique_ptr<TIRType> Type;

  public:
    explicit Parameter(std::unique_ptr<TIRName> Name,
                       std::unique_ptr<TIRType> Type, SourceLocation Loc)
        : TIRNode(TIRNodeKind::Name, Loc), Name(std::move(Name)),
          Type(std::move(Type)) {}
    static bool classof(const TIRNode *N) { return false; }
    auto getName() const -> const TIRName & { return *Name; }
    auto getType() const -> const TIRType & { return *Type; }
  };

  class TypeParameter : public TIRNode {
    std::unique_ptr<TIRType> Type;

  public:
    explicit TypeParameter(std::unique_ptr<TIRType> Type, SourceLocation Loc)
        : TIRNode(TIRNodeKind::Name, Loc), Type(std::move(Type)) {}
    static bool classof(const TIRNode *N) { return false; }
    auto getType() const -> const TIRType & { return *Type; }
  };

protected:
  bool IsIntrinsic;
  std::unique_ptr<TIRName> Name;
  std::vector<std::unique_ptr<TypeParameter>> TypeParameters;
  std::vector<std::unique_ptr<Parameter>> Parameters;
  std::unique_ptr<TIRType> ReturnType;
  std::vector<std::unique_ptr<TIRStmt>> Statements;

public:
  explicit TIRFunctionDecl(
      bool IsIntrinsic, std::unique_ptr<TIRName> Name,
      std::vector<std::unique_ptr<TypeParameter>> TypeParameters,
      std::vector<std::unique_ptr<Parameter>> Parameters,
      std::unique_ptr<TIRType> ReturnType,
      std::vector<std::unique_ptr<TIRStmt>> Statements, SourceLocation Loc)
      : TIRDecl(TIRNodeKind::FunctionDecl, Loc), IsIntrinsic(IsIntrinsic),
        Name(std::move(Name)), TypeParameters(std::move(TypeParameters)),
        Parameters(std::move(Parameters)), ReturnType(std::move(ReturnType)),
        Statements(std::move(Statements)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::FunctionDecl;
  }
  auto isIntrinsic() const -> bool { return IsIntrinsic; }
  auto getName() const -> const TIRName & { return *Name; }
  auto getTypeParameters() const
      -> const std::vector<std::unique_ptr<TypeParameter>> & {
    return TypeParameters;
  }
  auto getParameters() const
      -> const std::vector<std::unique_ptr<Parameter>> & {
    return Parameters;
  }
  auto getReturnType() const -> const TIRType & { return *ReturnType; }
  auto getStatements() const -> const std::vector<std::unique_ptr<TIRStmt>> & {
    return Statements;
  }
};

class TIRTypeDecl : public TIRDecl {
  std::unique_ptr<TIRName> Name;

public:
  explicit TIRTypeDecl(std::unique_ptr<TIRName> Name, SourceLocation Loc)
      : TIRDecl(TIRNodeKind::TypeDecl, Loc), Name(std::move(Name)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::TypeDecl;
  }
  auto getName() const -> const TIRName & { return *Name; }
};

class TIRStructDecl : public TIRDecl {
public:
  class Member : public TIRNode {
    std::unique_ptr<TIRName> Name;
    std::unique_ptr<TIRType> Type;

  public:
    explicit Member(std::unique_ptr<TIRName> Name,
                    std::unique_ptr<TIRType> Type, SourceLocation Loc)
        : TIRNode(TIRNodeKind::Name, Loc), Name(std::move(Name)),
          Type(std::move(Type)) {}
    static bool classof(const TIRNode *N) { return false; }
    auto getName() const -> const TIRName & { return *Name; }
    auto getType() const -> const TIRType & { return *Type; }
  };

protected:
  std::unique_ptr<TIRName> Name;
  std::vector<std::unique_ptr<Member>> Members;

public:
  explicit TIRStructDecl(std::unique_ptr<TIRName> Name,
                         std::vector<std::unique_ptr<Member>> Members,
                         SourceLocation Loc)
      : TIRDecl(TIRNodeKind::StructDecl, Loc), Name(std::move(Name)),
        Members(std::move(Members)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::StructDecl;
  }
  auto getName() const -> const TIRName & { return *Name; }
  auto getMembers() const -> const std::vector<std::unique_ptr<Member>> & {
    return Members;
  }
};

class TIRTraitDecl : public TIRDecl {
public:
  class TypeParameter : public TIRNode {
    std::unique_ptr<TIRName> Name;

  public:
    explicit TypeParameter(std::unique_ptr<TIRName> Name, SourceLocation Loc)
        : TIRNode(TIRNodeKind::Name, Loc), Name(std::move(Name)) {}
    static bool classof(const TIRNode *N) { return false; }
    auto getName() const -> const TIRName & { return *Name; }
  };

protected:
  std::unique_ptr<TIRName> Name;
  std::vector<std::unique_ptr<TypeParameter>> TypeParameters;
  std::vector<std::unique_ptr<TIRFunctionDecl>> Methods;

public:
  explicit TIRTraitDecl(
      std::unique_ptr<TIRName> Name,
      std::vector<std::unique_ptr<TypeParameter>> TypeParameters,
      std::vector<std::unique_ptr<TIRFunctionDecl>> Methods, SourceLocation Loc)
      : TIRDecl(TIRNodeKind::TraitDecl, Loc), Name(std::move(Name)),
        TypeParameters(std::move(TypeParameters)), Methods(std::move(Methods)) {
  }
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::TraitDecl;
  }
  auto getName() const -> const TIRName & { return *Name; }
  auto getTypeParameters() const
      -> const std::vector<std::unique_ptr<TypeParameter>> & {
    return TypeParameters;
  }
  auto getMethods() const
      -> const std::vector<std::unique_ptr<TIRFunctionDecl>> & {
    return Methods;
  }
};

class TIRInstanceDecl : public TIRDecl {
  std::unique_ptr<TIRName> Name;
  std::vector<std::unique_ptr<TIRType>> TypeArguments;
  std::unique_ptr<TIRType> SelfType;
  std::vector<std::unique_ptr<TIRFunctionDecl>> Methods;

public:
  explicit TIRInstanceDecl(
      std::unique_ptr<TIRName> Name,
      std::vector<std::unique_ptr<TIRType>> TypeArguments,
      std::unique_ptr<TIRType> SelfType,
      std::vector<std::unique_ptr<TIRFunctionDecl>> Methods, SourceLocation Loc)
      : TIRDecl(TIRNodeKind::InstanceDecl, Loc), Name(std::move(Name)),
        TypeArguments(std::move(TypeArguments)), SelfType(std::move(SelfType)),
        Methods(std::move(Methods)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() == TIRNodeKind::InstanceDecl;
  }
  auto getName() const -> const TIRName & { return *Name; }
  auto getTypeArguments() const
      -> const std::vector<std::unique_ptr<TIRType>> & {
    return TypeArguments;
  }
  auto getSelfType() const -> const TIRType & { return *SelfType; }
  auto getMethods() const
      -> const std::vector<std::unique_ptr<TIRFunctionDecl>> & {
    return Methods;
  }
};
} // namespace xd

#endif // XD_FRONTEND_TIR_H
