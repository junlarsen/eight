//===----- DiagnosticEmitter ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef DIAGNOSTICEMITTER_H
#define DIAGNOSTICEMITTER_H

#include "llvm/TableGen/Record.h"

namespace xd {
class DiagnosticEmitter {
  const llvm::RecordKeeper &RK;

  auto emitDiagnostic(const llvm::Record *Rec, llvm::raw_ostream &OS) -> void;
  auto
  emitDiagnosticIdentifiers(llvm::ArrayRef<const llvm::Record *> Recs) -> void;

public:
  explicit DiagnosticEmitter(const llvm::RecordKeeper &RK) : RK(RK) {}
  auto emit(llvm::raw_ostream &OS) -> bool;
};
} // namespace xd

#endif // DIAGNOSTICEMITTER_H
