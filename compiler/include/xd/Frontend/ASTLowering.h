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
class ASTLoweringPass {
  ScopeStack<std::string, int> Scopes;
  ASTTranslationUnit &TU;

public:
  explicit ASTLoweringPass(ASTTranslationUnit &TU) : TU(TU) {}

  auto run() -> std::unique_ptr<TIRModule>;
};
} // namespace xd

#endif
