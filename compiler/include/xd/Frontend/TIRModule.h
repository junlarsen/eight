//===----- TIRModule.h - TIR Translation Units ----- ----------------------===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_TIRMODULE_H
#define XD_FRONTEND_TIRMODULE_H

#include "xd/Frontend/TIR.h"
#include <map>

namespace xd {
/// A TIRModule represents a translation unit in the typed intermediate
/// representation.
class TIRModule {
  std::map<std::string, std::unique_ptr<TIRFunctionDecl>> Functions;
  std::map<std::string, std::unique_ptr<TIRTypeDecl>> Types;
  std::map<std::string, std::unique_ptr<TIRTraitDecl>> Traits;
  std::map<std::string, std::vector<std::unique_ptr<TIRInstanceDecl>>>
      Instances;
  std::map<std::string, std::unique_ptr<TIRStructDecl>> Structs;

public:
  explicit TIRModule() = default;

  auto addFunction(TIRQualifiedName& QN, std::unique_ptr<TIRFunctionDecl> Func) -> void;
  auto addType(TIRQualifiedName &QN, std::unique_ptr<TIRTypeDecl> Type) -> void;
  auto addTrait(TIRQualifiedName &QN, std::unique_ptr<TIRTraitDecl> Trait) -> void;
  auto addInstance(TIRQualifiedName &QN, std::string Trait, std::unique_ptr<TIRInstanceDecl> Instance)
      -> void;
  auto addStruct(TIRQualifiedName &QN, std::unique_ptr<TIRStructDecl> Struct) -> void;
};
} // namespace xd

#endif // XD_FRONTEND_TIRMODULE_H
