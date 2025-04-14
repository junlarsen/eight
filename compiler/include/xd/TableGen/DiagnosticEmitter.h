//===----- DiagnosticEmitter.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_TABLEGEN_DIAGNOSTICEMITTER_H
#define XD_TABLEGEN_DIAGNOSTICEMITTER_H

#include "llvm/TableGen/Record.h"

namespace xd {
class DiagnosticEmitter {
  const llvm::RecordKeeper &RK;

public:
  explicit DiagnosticEmitter(const llvm::RecordKeeper &RK) : RK(RK) {}
  auto emit(llvm::raw_ostream &OS) -> bool;
};
} // namespace xd

#endif // XD_TABLEGEN_DIAGNOSTICEMITTER_H
