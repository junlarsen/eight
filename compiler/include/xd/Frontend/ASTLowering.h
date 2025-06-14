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
template <class Key = std::string, class Value> class ScopeStack {
  std::deque<std::unordered_map<Key, Value>> Stack;

public:
  explicit ScopeStack() = default;
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
