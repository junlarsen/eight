//===----- DiagnosticManager.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Basic/DiagnosticManager.h"
#include "xd/Basic/Location.h"

using namespace xd;
using namespace llvm;

void DiagnosticManager::debug(raw_ostream &OS, SourceManager &SM) const {
  OS << "Diagnostic Manager has " << Diagnostics.size() << " diagnostics."
     << "\n";
  for (auto &Diagnostic : Diagnostics) {
    Diagnostic->emit(OS, SM);
  }
}
