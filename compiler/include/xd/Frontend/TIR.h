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

#include <cstdint>
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
  // Declaration nodes
  Decl,
  /// The module declaration node.
  ///
  /// It corresponds to a single AST translation unit. The entire AST
  /// translation unit is effectively flattened into a single TIR module.
  ModuleDecl,
  IntrinsicFunctionDecl,
  FunctionDecl,
  StructDecl,
  IntrinsicTypeDecl,
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
  Unknown,
  /// An error type, which is used to prevent further propagation of constraints
  /// in the unification algorithm when a type cannot be deduced.
  ///
  /// This is useful because we perform type-checking on partial syntax trees
  /// that may contain syntax errors. If we encounter something that's missing
  /// we give it TheHole, which cannot be unified with anything else.
  TheHole,
};

class TIRNode {
  TIRNodeKind Kind;

public:
  explicit TIRNode(TIRNodeKind Kind) : Kind(Kind) {}
  auto getKind() const -> TIRNodeKind { return Kind; }
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Decl &&
           N->getKind() <= TIRNodeKind::TheHole;
  }
};

class TIRTypeNode : public TIRNode {
public:
  explicit TIRTypeNode(TIRNodeKind Kind) : TIRNode(Kind) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Type &&
           N->getKind() <= TIRNodeKind::TheHole;
  }
};

/// Represents any expression node in the TIR.
///
/// All expressions are of some type, so the type is stored on this class.
class TIRExprNode : public TIRNode {
  std::unique_ptr<TIRTypeNode> Type;

public:
  explicit TIRExprNode(TIRNodeKind Kind, std::unique_ptr<TIRTypeNode> Type)
      : TIRNode(Kind), Type(std::move(Type)) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Expr &&
           N->getKind() <= TIRNodeKind::ConstructionExpr;
  }

  /// Get the type of this expression node.
  auto getType() const -> const TIRTypeNode * { return Type.get(); }
};

class TIRStmtNode : public TIRNode {
public:
  explicit TIRStmtNode(TIRNodeKind Kind) : TIRNode(Kind) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Stmt &&
           N->getKind() <= TIRNodeKind::ExprStmt;
  }
};

class TIRDeclNode : public TIRNode {
public:
  explicit TIRDeclNode(TIRNodeKind Kind) : TIRNode(Kind) {}
  static bool classof(const TIRNode *N) {
    return N->getKind() >= TIRNodeKind::Decl &&
           N->getKind() <= TIRNodeKind::InstanceDecl;
  }
};
} // namespace xd

#endif // XD_FRONTEND_TIR_H
