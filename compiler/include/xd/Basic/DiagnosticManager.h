//===----- DiagnosticManager.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_BASIC_DIAGNOSTICMANAGER_H
#define XD_BASIC_DIAGNOSTICMANAGER_H

#include "xd/Basic/Diagnostics.td.inc"
#include <cstdint>
#include <memory>
#include <vector>

namespace xd {
using DiagnosticID = uint32_t;

struct DiagnosticOptions {
  uint32_t MaxDiagnostics;
};

class DiagnosticManager {
  std::vector<std::unique_ptr<Diagnostic>> Diagnostics;

public:
  DiagnosticManager() {}
  DiagnosticManager(const DiagnosticManager &) = delete;

  /// Report a new diagnostic to the DiagnosticManager.
  template <class D, class... Args> auto report(Args &&...A) -> DiagnosticID {
    std::unique_ptr<Diagnostic> Diag =
        std::make_unique<D>(std::forward<Args>(A)...);
    DiagnosticID ID = Diagnostics.size();
    Diagnostics.push_back(std::move(Diag));
    return ID;
  }

  auto isEmpty() const -> bool { return Diagnostics.empty(); }
  auto diagnostics() const -> const std::vector<std::unique_ptr<Diagnostic>> * {
    return &Diagnostics;
  }
};
} // namespace xd

#endif // XD_BASIC_DIAGNOSTICMANAGER_H
