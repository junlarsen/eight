//===----- Diagnostic.h.inc ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file does not declare a namespace because it's included in-place by the
// Diagnostic TableGen emitter.
//
//===----------------------------------------------------------------------===//

class Diagnostic {
  DiagnosticKind Kind;

public:
  explicit Diagnostic(DiagnosticKind Kind) : Kind(Kind) {}
  auto getKind() const -> DiagnosticKind { return Kind; }
  static bool classof(const Diagnostic *Diag) {
    return Diag->getKind() >= FirstDiagnosticKind &&
           Diag->getKind() <= LastDiagnosticKind;
  }
};
