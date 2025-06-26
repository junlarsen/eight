//===----- ASTLowering.h - Lowering of AST to TIR -------------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_ASTLOWERING_H
#define XD_FRONTEND_ASTLOWERING_H

#include "xd/Frontend/TIRModule.h"
#include "xd/Frontend/TranslationUnit.h"
#include <deque>
#include <unordered_map>

namespace xd {
/// A FIFO stack of scopes used for name resolution and symbol lookup.
template <class Key, class Value> class ScopeStack {
  std::deque<std::unordered_map<Key, Value>> Stack;

public:
  explicit ScopeStack() = default;

  auto enter() -> void { Stack.emplace_back(); }
  auto exit() -> void {
    assert(!Stack.empty() && "Cannot exit an empty stack");
    Stack.pop_back();
  }

  /// Insert a value into the current scope.
  auto insert(Key K, Value V) -> void {
    assert(!Stack.empty() && "Cannot insert into an empty scope stack");
    Stack.back().insert({std::move(K), std::move(V)});
  }
  /// Remove a key from the current scope, if it exists.
  auto remove(const Key &K) -> void {
    assert(!Stack.empty() && "Cannot remove from an empty scope stack");
    Stack.back().erase(K);
  }
  /// Try searching for a key in the current scope stack, starting from the
  /// innermost scope.
  auto search(const Key &K) const -> std::optional<Value> {
    for (auto It = Stack.rbegin(); It != Stack.rend(); ++It) {
      auto Found = It->find(K);
      if (Found != It->end())
        return Found->second;
    }
    return std::nullopt; // Not found in any scope
  }
};

/// A pass that lowers a single AST translation unit into a single untyped TIR
/// module.
///
/// This pass runs in two phases, one for forward declaration and legality check
/// of declarations, and another for the actual lowering of the translation
/// unit.
///
/// It is up to each `enterXXXDecl` function to determine whether the
/// declaration is valid and can be (partially or fully) lowered, or if it lacks
/// enough information.
///
/// A broken FunctionDecl parsed from the code `fn` cannot be used, because
/// there is no name to refer to it, but `fn foo(` can be used and forward
/// declared to `FunctionDecl` with a name foo, zero arguments, and an error
/// return type.
///
/// This is all sound because the code generator will never run if there are
/// frontend errors in the diagnostic manager after type checking. A single
/// error type in the tree will signal that the translation unit is malformed.
///
/// All of this effort is done so that the end programmer can write broken or
/// partial code, and still get both syntax, type, and semantic errors from the
/// compiler and into their editor.
class ASTLoweringPass {
  SourceManager &SM;

  ScopeStack<std::string, TIRName> Scopes;
  std::unique_ptr<TIRModule> Module;

public:
  explicit ASTLoweringPass(SourceManager &SM)
      : SM(SM), Scopes({}), Module(std::make_unique<TIRModule>()) {}

  /// Run the lowering pass on the translation unit, returning a TIR module.
  auto run(ASTTranslationUnit &TU) -> std::unique_ptr<TIRModule>;

  auto visitTranslationUnit(ASTTranslationUnit &TU) -> void;
  auto enterDecl(ASTDecl &D, ModuleGraphNode &MGN) -> void;
  auto enterFileDecl(ASTFileDecl &MD, ModuleGraphNode &MGN) -> void;
  auto enterImportDecl(ASTImportDecl &ID, ModuleGraphNode &MGN) -> void;
  auto enterFunctionDecl(ASTFunctionDecl &FD, ModuleGraphNode &MGN) -> void;
  auto enterStructDecl(ASTStructDecl &SD, ModuleGraphNode &MGN) -> void;
  auto enterIntrinsicTypeDecl(ASTIntrinsicTypeDecl &ITD, ModuleGraphNode &MGN)
      -> void;
  auto enterTraitDecl(ASTTraitDecl &TD) -> void;
  auto enterInstanceDecl(ASTInstanceDecl &ID) -> void;

  auto leaveDecl(ASTDecl &D) -> void;
  auto leaveFileDecl(ASTFileDecl &MD) -> void;
  auto leaveImportDecl(ASTImportDecl &ID) -> void;
  auto leaveFunctionDecl(ASTFunctionDecl &FD) -> void;
  auto leaveStructDecl(ASTStructDecl &SD) -> void;
  auto leaveIntrinsicTypeDecl(ASTIntrinsicTypeDecl &ITD) -> void;
  auto leaveTraitDecl(ASTTraitDecl &TD) -> void;
  auto leaveInstanceDecl(ASTInstanceDecl &ID) -> void;

  auto visitStmt(ASTStmt &S) -> void;
  auto visitType(ASTType &T) -> void;
  auto visitExpr(ASTExpr &E) -> void;
};
} // namespace xd

#endif
